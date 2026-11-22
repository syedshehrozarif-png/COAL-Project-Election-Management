TITLE Digital Election System (MASM / Irvine32)       (ElectionSystem.asm)

; ====================================================================
;  COAL End-of-Semester Project - Digital Election System  (v2)
;  Language : MASM x86 (32-bit) using the Irvine32 library
;
;  Original features
;    * Voter login  : name, age (>= 18), 13-digit numeric CNIC
;    * Role menu    : User / Admin Panel
;    * User         : show candidates, cast ONE vote per CNIC
;    * Admin        : password (3 attempts, 1-hour lockout), results,
;                     graph, add / remove candidate, voters list,
;                     end elections, save + exit
;    * Persistence  : binary files, coloured console output
;
;  New in v2
;    * Masked password entry (ReadChar, shows '*')
;    * STRUCT Candidate / STRUCT Voter instead of parallel arrays
;    * Candidates live on the heap (HeapAlloc / HeapFree), max 8
;    * Audit log with timestamps (GetLocalTime + SYSTEMTIME)
;    * Win32 Beep on successful vote / errors / failed login
;    * Age is reduced to an age GROUP; CNIC decoded into gender/region;
;      all packed in one DWORD of bit flags per voter (BT/BTS/AND/OR/SHL)
;    * Admin password stored only as a hash (ROL / XOR / SHL) + change-password
;    * Percentages: integer % with DIV, one-decimal % with the FPU
;    * Turnout statistics by gender / age group / region
;    * Hash table (CNIC mod 101 using DIV, linear probing) for "has voted"
;    * Consistency audit: sum(votes) + withdrawn votes must equal voters
;    * "Check if my CNIC has voted" for users
;    * Colour-coded VERTICAL bar graph
;    * CSV export, loading animation (CR redraw + Delay)
; ====================================================================

INCLUDE Irvine32.inc

; Win32 Beep (kernel32). Identical re-declaration is harmless if the
; include file already has it.
Beep PROTO, dwFreq:DWORD, dwDuration:DWORD

IFNDEF HEAP_ZERO_MEMORY
HEAP_ZERO_MEMORY EQU 00000008h
ENDIF

; --------------------------------------------------------------------
;  Constants
; --------------------------------------------------------------------
MAX_CAND     EQU 8             ; hard policy limit on candidates
NAME_LEN     EQU 50            ; bytes reserved per candidate name
MAX_VOTERS   EQU 100           ; maximum number of voters stored
CNIC_LEN     EQU 20            ; bytes reserved per CNIC string
CNIC_DIGITS  EQU 13            ; a valid CNIC has exactly 13 digits
HASH_SIZE    EQU 101           ; prime size of the voter hash table
LOCK_MS      EQU 3600000       ; admin lockout = 1 hour in milliseconds
DAY_MS       EQU 86400000      ; GetMseconds wraps at midnight
BUF_SIZE     EQU 128           ; size of every keyboard input buffer
READ_MAX     EQU 100           ; max characters read per line (< BUF_SIZE)
MAX_AGE      EQU 120           ; oldest age accepted at login
PASS_MIN     EQU 6             ; minimum length of a new admin password
GRAPH_H      EQU 10            ; rows in the vertical bar graph

; Default admin hash = HashStr("admin123")  (plaintext is NOT in this file)
DEFAULT_PASS_HASH EQU 620191F6h
HASH_SEED    EQU 5381

; Voter flag bits (one DWORD per voter)
VF_VOTED     EQU 0             ; bit 0   : has voted
VF_MALE      EQU 1             ; bit 1   : 1 = male (odd last CNIC digit)
VF_AGE_SH    EQU 2             ; bits 2-3: age group 0..3
VF_REG_SH    EQU 4             ; bits 4-7: region = first CNIC digit (1..7, else 0)

; CreateFile values for the append-only audit log
LOG_ACCESS   EQU 4             ; FILE_APPEND_DATA (writes always go to the end)
LOG_SHARE    EQU 1             ; FILE_SHARE_READ
LOG_DISP     EQU 4             ; OPEN_ALWAYS (create if missing)
LOG_ATTR     EQU 80h           ; FILE_ATTRIBUTE_NORMAL

NL         EQU <0Dh,0Ah>

; Console colours
CLR_GRAY     EQU 7
CLR_RED      EQU 4
CLR_GREEN    EQU 2
CLR_LGREEN   EQU 10
CLR_CYAN     EQU 3
CLR_LCYAN    EQU 11
CLR_YELLOW   EQU 14
CLR_BROWN    EQU 6
CLR_LMAG     EQU 13

; --------------------------------------------------------------------
;  Structures
;  (note: "name" is a reserved word in MASM, so the field is "cname")
; --------------------------------------------------------------------
Candidate STRUCT
    cname BYTE NAME_LEN DUP(0)
    votes DWORD 0
Candidate ENDS

Voter STRUCT
    cnic  BYTE CNIC_LEN DUP(0)
    flags DWORD 0
Voter ENDS

; --------------------------------------------------------------------
;  Macros
; --------------------------------------------------------------------
SetColor MACRO clr                  ; change text colour (EAX preserved)
    push eax
    mov  eax, clr
    call SetTextColor
    pop  eax
ENDM

PrintStr MACRO txt                  ; print a null-terminated string (EDX preserved)
    push edx
    mov  edx, OFFSET txt
    call WriteString
    pop  edx
ENDM

PrintClr MACRO clr, txt             ; print string in a colour, then back to gray
    SetColor clr
    PrintStr txt
    SetColor CLR_GRAY
ENDM

PrintErr MACRO txt                  ; red message + error beep
    SetColor CLR_RED
    PrintStr txt
    SetColor CLR_GRAY
    call BeepError
ENDM

LogMsg MACRO txt                    ; write one line to the audit log
    push esi
    push edx
    mov  esi, OFFSET txt
    xor  edx, edx
    call LogEvent
    pop  edx
    pop  esi
ENDM

LogMsgCnic MACRO txt                ; audit line + the current user's CNIC
    push esi
    push edx
    mov  esi, OFFSET txt
    mov  edx, OFFSET CurrentUserCNIC
    call LogEvent
    pop  edx
    pop  esi
ENDM

PutCh MACRO c                       ; store one character at [EDI], advance EDI
    mov  BYTE PTR [edi], c
    inc  edi
ENDM

; ====================================================================
.data
; ====================================================================

; ---------- Election data (candidates live on the heap) ----------
hHeap           DWORD 0                           ; process heap handle
candPtr         DWORD MAX_CAND DUP(0)             ; pointers to Candidate blocks
totalCandidates DWORD 0
removedVotes    DWORD 0                           ; votes of removed candidates (audit)

; ---------- Voter data ----------
totalVoters     DWORD 0
voters          Voter MAX_VOTERS DUP(<>)          ; CNIC + packed flags
hashTable       DWORD HASH_SIZE DUP(0)            ; slot = voter index + 1 (0 = empty)
CurrentUserCNIC BYTE  CNIC_LEN DUP(0)
CurrentAgeGrp   DWORD 0
CurrentFlags    DWORD 0

; ---------- Statistics ----------
genderCount     DWORD 2 DUP(0)                    ; [0] female  [1] male
ageCount        DWORD 4 DUP(0)
regionCount     DWORD 8 DUP(0)

; ---------- Files ----------
electionFile    BYTE "election_data.dat",0
cnicFile        BYTE "voted_cnic.dat",0
hashFile        BYTE "admin_hash.dat",0
logFile         BYTE "audit_log.txt",0
csvFile         BYTE "results.csv",0
fileHandle      DWORD ?
logHandle       DWORD ?
logLen          DWORD ?
loadOk          DWORD 0           ; 1 if election_data.dat was loaded successfully

; ---------- Admin security ----------
AdminHash       DWORD DEFAULT_PASS_HASH
failedAttempts  DWORD 0
lockoutStart    DWORD 0
tamperFlag      DWORD 0
auditSum        DWORD 0

; ---------- Input / work buffers ----------
inputBuf        BYTE BUF_SIZE DUP(0)
nameBuf         BYTE BUF_SIZE DUP(0)
cnicBuf         BYTE BUF_SIZE DUP(0)
passBuf         BYTE BUF_SIZE DUP(0)
passBuf2        BYTE BUF_SIZE DUP(0)
passBuf3        BYTE BUF_SIZE DUP(0)
logBuf          BYTE 256 DUP(0)
outBuf          BYTE 512 DUP(0)
tmpBuf          BYTE 32 DUP(0)
readBuf         BYTE 1024 DUP(0)
sysTime         SYSTEMTIME <>
expTotal        DWORD 0

; ---------- FPU scratch ----------
fpuNum          DWORD ?
fpuDen          DWORD ?
fpuOut          DWORD ?
k1000           DWORD 1000

; ---------- Graph ----------
graphH          DWORD MAX_CAND DUP(0)
barColors       BYTE 12,10,9,14,13,11,6,5         ; one colour per candidate slot
spinner         BYTE "|/-\"

; ---------- Default candidates ----------
defName1        BYTE "Sir Abdullah",0
defName2        BYTE "Sir Shaheer",0
defName3        BYTE "Sir Shehroz",0
defName4        BYTE "Sir Talha", 0

; ---------- Constant strings ----------
strYes          BYTE "yes",0
strY            BYTE "y",0

; ---------- Admin jump table (menu options 1..12) ----------
; (kept as ONE logical list with trailing commas so LENGTHOF sees every entry)
adminTable      DWORD OFFSET DisplayCandidates, OFFSET ShowResults,
                      OFFSET ShowGraph, OFFSET AddCandidate,
                      OFFSET RemoveCandidate, OFFSET DisplayVoters,
                      OFFSET ShowStats, OFFSET ExportResults,
                      OFFSET IntegrityReport, OFFSET ChangePassword,
                      OFFSET ShowAuditLog, OFFSET EndVoting
ADMIN_N         EQU LENGTHOF adminTable          ; = 12 ; N+1 = main menu, N+2 = exit

; ---------- Label tables for statistics ----------
ageS0   BYTE "Age 18-25",0
ageS1   BYTE "Age 26-40",0
ageS2   BYTE "Age 41-60",0
ageS3   BYTE "Age 61+  ",0
ageNames DWORD OFFSET ageS0, OFFSET ageS1, OFFSET ageS2, OFFSET ageS3

rg0     BYTE "Other / Unknown     ",0
rg1     BYTE "Khyber Pakhtunkhwa  ",0
rg2     BYTE "FATA (tribal areas) ",0
rg3     BYTE "Punjab              ",0
rg4     BYTE "Sindh               ",0
rg5     BYTE "Balochistan         ",0
rg6     BYTE "Islamabad           ",0
rg7     BYTE "Gilgit-Baltistan    ",0
regionNames DWORD OFFSET rg0, OFFSET rg1, OFFSET rg2, OFFSET rg3,
                  OFFSET rg4, OFFSET rg5, OFFSET rg6, OFFSET rg7

strMale   BYTE "Male  ",0
strFemale BYTE "Female",0

; ---------- Banners ----------
artWelcome BYTE "=====================================================", NL
                BYTE "         WELCOME TO THE ONLINE ELECTION SYSTEM       ", NL
                BYTE "=====================================================", NL, NL, 0

artAdmin   BYTE "              _           _         _____                 _ ", NL
                BYTE "     /\      | |         (_)       |  __ \               | |", NL
                BYTE "    /  \   __| |_ __ ___  _ _ __   | |__) |_ _ _ __   ___| |", NL
                BYTE "   / /\ \ / _` | '_ ` _ \| | '_ \  |  ___/ _` | '_ \ / _ \ |", NL
                BYTE "  / ____ \ (_| | | | | | | | | | | | |  | (_| | | | |  __/ |", NL
                BYTE " /_/    \_\__,_|_| |_| |_|_|_| |_| |_|   \__,_|_| |_|\___|_|", NL, NL, 0

artUser    BYTE "  _   _                            _   _    _                 __  __                  ", NL
                BYTE " | \ | |                          | | | |  | |               |  \/  |                 ", NL
                BYTE " |  \| | ___  _ __ _ __ ___   __ _| | | |  | |___  ___ _ __  | \  / | ___ _ __  _   _ ", NL
                BYTE " | . ` |/ _ \| '__| '_ ` _ \ / _` | | | |  | / __|/ _ \ '__| | |\/| |/ _ \ '_ \| | | |", NL
                BYTE " | |\  | (_) | |  | | | | | | (_| | | | |__| \__ \  __/ |    | |  | |  __/ | | | |_| |", NL
                BYTE " |_| \_|\___/|_|  |_| |_| |_|\__,_|_|  \____/|___/\___|_|    |_|  |_|\___|_| |_|\__,_|", NL, NL, 0

artCand    BYTE NL
                BYTE " __             __     __       ___  ___  __             __  ___ ", NL
                BYTE "/  `  /\  |\ | |  \ | |  \  /\   |  |__  /__`    |    | /__`  |  ", NL
                BYTE "\__, /~~\ | \| |__/ | |__/ /~~\  |  |___ .__/    |___ | .__/  |  ", NL, NL, 0

artResults BYTE NL
                BYTE " ___       ___  __  ___    __           __   ___  __            ___ ", NL
                BYTE "|__  |    |__  /  `  |  | /  \ |\ |    |__) |__  /__` |  | |     |  ", NL
                BYTE "|___ |___ |___ \__,  |  | \__/ | \|    |  \ |___ .__/ \__/ |___  |  ", NL, NL, 0

artGraph   BYTE NL
                BYTE "------------- ELECTION RESULTS (VERTICAL GRAPH) -------------", NL, NL, 0

artVoters  BYTE "      __  ___  ___  __             __  ___ ", NL
                BYTE "\  / /  \  |  |__  |__)    |    | /__`  |  ", NL
                BYTE " \/  \__/  |  |___ |  \    |___ | .__/  |  ", NL, NL, 0

artFinal   BYTE "  ______ _             _  __      __   _          _____                  _     ", NL
                BYTE " |  ____(_)           | | \ \    / /  | |        / ____|                | |  _ ", NL
                BYTE " | |__   _ _ __   __ _| |  \ \  / /__ | |_ ___  | |     ___  _   _ _ __ | |_(_) ", NL
                BYTE " |  __| | | '_ \ / _` | |   \ \/ / _ \| __/ _ \ | |    / _ \| | | | '_ \| __|   ", NL
                BYTE " | |    | | | | | (_| | |    \  / (_) | ||  __/ | |___| (_) | |_| | | | | |_ _  ", NL
                BYTE " |_|    |_|_| |_|\__,_|_|     \/ \___/ \__\___|  \_____\___/ \__,_|_| |_|\__(_) ", NL, NL, 0

artStats   BYTE NL, "------------------- TURNOUT STATISTICS -------------------", NL, NL, 0
artLog     BYTE NL, "---------------------- AUDIT LOG ----------------------", NL, NL, 0
artInteg   BYTE NL, "------------------ DATA INTEGRITY CHECK ------------------", NL, NL, 0

; ---------- Menus ----------
msgRoleMenu BYTE "Choose your role:", NL
                BYTE "1. User", NL
                BYTE "2. Admin Panel", NL
                BYTE "Enter choice: ", 0

menuUser    BYTE "1. Show Candidates", NL
                BYTE "2. Cast a Vote", NL
                BYTE "3. Check if my CNIC has voted", NL
                BYTE "4. Go to Main Menu", NL
                BYTE "5. Exit", NL
                BYTE "Enter your Choice: ", 0

menuAdmin   BYTE " 1. Show Candidates", NL
                BYTE " 2. Show Results (with percentages)", NL
                BYTE " 3. Show Results (vertical colour graph)", NL
                BYTE " 4. Add Candidate", NL
                BYTE " 5. Remove Candidate", NL
                BYTE " 6. Show Voters List", NL
                BYTE " 7. Turnout Statistics (gender / age / region)", NL
                BYTE " 8. Export Results (CSV)", NL
                BYTE " 9. Integrity Check", NL
                BYTE "10. Change Admin Password", NL
                BYTE "11. View Audit Log", NL
                BYTE "12. End Elections", NL
                BYTE "13. Go to Main Menu", NL
                BYTE "14. Save and Exit", NL
                BYTE "Enter your Choice: ", 0

; ---------- Messages ----------
msgName         BYTE "Enter your Name: ",0
msgAge          BYTE "Enter your Age: ",0
msgCnic         BYTE "Enter your 13-digit CNIC Number: ",0
msgInvalidNum   BYTE "Invalid Input! Please Enter a Number.",NL,0
msgUnderAge     BYTE "Age does not meet Minimum Requirement",NL,0
msgBadCnic      BYTE "Invalid CNIC! Only 13 Digit Numerical CNIC allowed.",NL,0
msgRoleInvalid  BYTE "Invalid Input! Please enter 1 or 2.",NL,0
msgInvalidChoice BYTE "Invalid choice!",NL,0
msgGoMain       BYTE "Going to Main Menu..",NL,0
msgGoodbye      BYTE "Goodbye!",NL,0
msgSavedExit    BYTE "Data saved. Exiting...",NL,0
msgSaveErr      BYTE "Error saving data.",NL,0

msgAdminPass    BYTE "Enter Admin Password: ",0
msgWrongPass    BYTE "Incorrect password! Attempts left: ",0
msgGranted      BYTE "Access Granted!",NL,0
msgDenied       BYTE "Access Denied! Try again in 1 hour.",NL,0
msgLocked       BYTE "Admin panel is locked after too many failed attempts.",NL,0

msgOldPass      BYTE "Enter CURRENT admin password: ",0
msgNewPass      BYTE "Enter NEW password (min 6 characters): ",0
msgConfirmPass  BYTE "Confirm NEW password: ",0
msgWrongOld     BYTE "Current password is wrong. Password not changed.",NL,0
msgPassShort    BYTE "New password is too short (minimum 6 characters).",NL,0
msgPassNoMatch  BYTE "The two new passwords do not match.",NL,0
msgPassChanged  BYTE "Password changed. Only its hash is stored.",NL,0

msgVerifyCnic   BYTE "Enter your 13-digit CNIC to verify: ",0
msgMismatch     BYTE "CNIC Mismatch! Login and Voting CNICS are not the SAME!",NL,0
msgAlreadyVoted BYTE "This CNIC has already voted! You cannot vote again.",NL,0
msgEnterVote    BYTE "Enter the number of the candidate you want to vote for: ",0
msgYouVoted     BYTE "You voted for ",0
msgThanks       BYTE ". Thank you!",NL,0
msgBadCand      BYTE "Invalid candidate number. Vote not counted.",NL,0
msgRegFull      BYTE "Voter registry is full. No more votes can be recorded.",NL,0
msgNoCand       BYTE "There are no candidates available.",NL,0
msgNoVoters     BYTE "No voters have voted yet.",NL,0
msgBadName      BYTE "Invalid name! Letters only (spaces . - ' allowed), must start with a letter, max 49 characters.",NL,0
msgBadAge       BYTE "Invalid age! Please enter a realistic age (18-120).",NL,0
msgDupCand      BYTE "That candidate already exists.",NL,0
msgYouHaveVoted BYTE "Your CNIC HAS already voted.",NL,0
msgNotVotedYet  BYTE "Your CNIC has NOT voted yet.",NL,0

msgColon        BYTE ": ",0
msgVotes        BYTE " votes",0
msgOpenParen    BYTE " (",0
msgCloseNl      BYTE ")",NL,0
msgPctClose     BYTE "%)",NL,0
msgLeading      BYTE NL,"Currently leading: ",0
msgWinner       BYTE NL,"WINNER: ",0
msgWith         BYTE " with ",0
msgVotesDot     BYTE " votes.",NL,0
msgTie          BYTE NL,"There is a tie between the top candidates!",NL,0
msgTurnout      BYTE NL,"Voter turnout: ",0
msgSlash        BYTE " / ",0

msgNewName      BYTE "Enter name of the new candidate: ",0
msgMaxCand      BYTE "Maximum number of candidates (8) reached.",NL,0
msgAdded        BYTE "Candidate added successfully.",NL,0
msgAllocFail    BYTE "Out of memory: could not allocate the candidate.",NL,0
msgRemoveWhich  BYTE "Enter the number of the candidate you want to remove: ",0
msgInvalidCand  BYTE "Invalid candidate number.",NL,0
msgRemoved      BYTE "Candidate removed successfully.",NL,0

msgSure         BYTE NL,"Are you sure you want to continue? Voting will end Entirely. (Yes to Continue): ",0
msgVerifyAdmin  BYTE NL,"Verify Your CNIC: ",0
msgEnded        BYTE NL,"Elections have Ended! Proceed to next page to view results",NL,0
msgDeclined     BYTE "Admin Declined Election Cancellation.",NL,0
msgCnicMismatch BYTE "CNIC MISMATCH! Elections not Ended!",NL,0
msgPassMismatch BYTE "Password MisMatch. Elections not Ended!",NL,0

msgGenderHdr    BYTE "Turnout by gender (last CNIC digit: odd = male, even = female):",NL,0
msgAgeHdr       BYTE NL,"Turnout by age group (exact age is never stored):",NL,0
msgRegHdr       BYTE NL,"Turnout by region (first CNIC digit):",NL,0

msgIntVotes     BYTE "Votes held by current candidates : ",0
msgIntRemoved   BYTE "Votes of removed candidates       : ",0
msgIntVoters    BYTE "Voters recorded                   : ",0
msgIntOk        BYTE NL,"RESULT: data is consistent (votes + withdrawn = voters).",NL,0
msgIntBad       BYTE NL,"RESULT: MISMATCH - files were edited, deleted or corrupted!",NL,0
msgTamperBanner BYTE "*** WARNING: integrity check FAILED - vote totals do not match the voter list! ***",NL,NL,0

msgScale        BYTE NL,"Bar heights are relative to the leader (tallest bar = ",0
msgScale2       BYTE " votes).",NL,0
msgNoLog        BYTE "No audit log exists yet.",NL,0
msgExported     BYTE "Results exported to results.csv",NL,0

msgLoadData     BYTE "Loading election data ",0
msgCounting     BYTE "Counting votes        ",0

csvHeader       BYTE "Candidate,Votes,Percent",0
csvTotalVoters  BYTE "Total voters,",0
csvWithdrawn    BYTE "Withdrawn votes (removed candidates),",0
csvTurnout      BYTE "Turnout percent of MAX_VOTERS,",0
csvResult       BYTE "Result,",0
csvTie          BYTE "TIE",0
csvNone         BYTE "NONE",0

; ---------- Audit log texts ----------
logStart        BYTE "PROGRAM STARTED",0
logExit         BYTE "PROGRAM EXIT",0
logLogin        BYTE "VOTER LOGIN OK, CNIC",0
logUnderAge     BYTE "LOGIN REJECTED (under age)",0
logAdminOk      BYTE "ADMIN LOGIN OK",0
logAdminFail    BYTE "ADMIN LOGIN FAILED (wrong password)",0
logAdminLock    BYTE "ADMIN PANEL LOCKED (3 failed attempts)",0
logVote         BYTE "VOTE CAST, CNIC",0
logDupVote      BYTE "DUPLICATE VOTE BLOCKED, CNIC",0
logCnicMismatch BYTE "VOTE REJECTED (CNIC mismatch), login CNIC",0
logCandAdded    BYTE "CANDIDATE ADDED:",0
logCandRemoved  BYTE "CANDIDATE REMOVED:",0
logPassChanged  BYTE "ADMIN PASSWORD CHANGED",0
logPassFail     BYTE "PASSWORD CHANGE REFUSED (wrong current password)",0
logExport       BYTE "RESULTS EXPORTED TO results.csv",0
logTamper       BYTE "INTEGRITY CHECK FAILED (votes do not match voters)",0
logEnded        BYTE "ELECTION ENDED BY ADMIN",0

; ====================================================================
.code
; ====================================================================

; --------------------------------------------------------------------
;  main : load saved data, then loop: login -> role menu -> back to login
; --------------------------------------------------------------------
main PROC
    finit                           ; clean FPU state for the percentage code
    invoke GetProcessHeap
    mov  hHeap, eax

    call LoadAdminHash              ; custom password hash, if one was saved
    call LoadElectionData           ; candidates + votes (sets loadOk)
    call LoadCNICData               ; voters who already voted
    cmp  loadOk, 1                  ; election file missing/corrupt -> old voter
    je   mainDataOk                 ; list no longer matches the votes: reset it
    call ClearVoters
    call SaveCNICData
mainDataOk:
    cmp  totalCandidates, 0         ; first run? create default candidates
    jne  mainHasCand
    call InitDefaultCandidates
    call SaveElectionData
mainHasCand:
    call RebuildHash                ; hash table is derived data, never saved
    call CheckIntegrity             ; sum(votes) + withdrawn == voters ?
    LogMsg logStart

    mov  edx, OFFSET msgLoadData
    call LoadingAnim
    call Clrscr
    cmp  tamperFlag, 0
    je   mainLoop
    PrintErr msgTamperBanner
    call WaitMsg
    call Clrscr

mainLoop:
    call LoginScreen                ; EAX = 1 if login OK, 0 if rejected
    cmp  eax, 0
    je   mainRestart
    call RoleMenu                   ; returns when user logs out / goes to main menu
mainRestart:
    call WaitMsg                    ; "Press any key to continue..."
    call Clrscr
    jmp  mainLoop
main ENDP

; --------------------------------------------------------------------
;  QuitProgram : save, release heap blocks, log, terminate
; --------------------------------------------------------------------
QuitProgram PROC
    call SaveElectionData
    call FreeCandidates
    LogMsg logExit
    exit
QuitProgram ENDP

; --------------------------------------------------------------------
;  Heap management for candidates
; --------------------------------------------------------------------

; AppendCandidate : ESI = name -> allocates a Candidate on the heap,
;   copies the name, votes = 0 (HEAP_ZERO_MEMORY), appends it.
;   EAX = 1 on success, 0 if full / out of memory
AppendCandidate PROC
    push ebx
    push edi
    push esi
    cmp  totalCandidates, LENGTHOF candPtr
    jae  apFail
    invoke HeapAlloc, hHeap, HEAP_ZERO_MEMORY, SIZEOF Candidate
    test eax, eax
    jz   apFail
    mov  ebx, totalCandidates
    mov  candPtr[ebx*4], eax
    mov  edi, eax                   ; cname is the first field (offset 0)
    call StrCopy                    ; ESI = name already
    inc  totalCandidates
    mov  eax, 1
    jmp  apExit
apFail:
    xor  eax, eax
apExit:
    pop  esi
    pop  edi
    pop  ebx
    ret
AppendCandidate ENDP

; FreeCandidates : HeapFree every allocated block (walks the whole pointer
;   array, so it is safe even if totalCandidates is garbage)
FreeCandidates PROC
    pushad
    xor  ebx, ebx
fcLoop:
    cmp  ebx, LENGTHOF candPtr
    jae  fcDone
    mov  esi, candPtr[ebx*4]
    test esi, esi
    jz   fcNext
    invoke HeapFree, hHeap, 0, esi
    mov  candPtr[ebx*4], 0
fcNext:
    inc  ebx
    jmp  fcLoop
fcDone:
    popad
    ret
FreeCandidates ENDP

; ClearElection : free candidates, zero pointers, counters
ClearElection PROC
    pushad
    call FreeCandidates
    cld
    xor  eax, eax
    mov  edi, OFFSET candPtr
    mov  ecx, LENGTHOF candPtr
    rep  stosd
    mov  totalCandidates, 0
    mov  removedVotes, 0
    popad
    ret
ClearElection ENDP

; ClearVoters : zero voter count, voter records and the hash table
ClearVoters PROC
    pushad
    cld
    xor  eax, eax
    mov  totalVoters, 0
    mov  edi, OFFSET voters
    mov  ecx, SIZEOF voters
    rep  stosb
    mov  edi, OFFSET hashTable
    mov  ecx, LENGTHOF hashTable
    rep  stosd
    popad
    ret
ClearVoters ENDP

; --------------------------------------------------------------------
;  InitDefaultCandidates : 4 starter candidates, all votes = 0
; --------------------------------------------------------------------
InitDefaultCandidates PROC
    pushad
    call ClearElection              ; wipe any leftover/garbage data first
    mov  esi, OFFSET defName1
    call AppendCandidate
    mov  esi, OFFSET defName2
    call AppendCandidate
    mov  esi, OFFSET defName3
    call AppendCandidate
    mov  esi, OFFSET defName4
    call AppendCandidate
    popad
    ret
InitDefaultCandidates ENDP

; --------------------------------------------------------------------
;  LoginScreen : name, age, CNIC.  Returns EAX = 1 (ok) / 0 (rejected)
;  The exact age is validated and reduced to an age GROUP; it is never kept.
; --------------------------------------------------------------------
LoginScreen PROC
    push ecx
    push edx
    push esi
    push edi

    SetColor CLR_LCYAN
    PrintStr artWelcome
    SetColor CLR_GRAY

lsName:                             ; ---- name ----
    PrintStr msgName
    mov  edx, OFFSET nameBuf
    mov  ecx, READ_MAX
    call ReadString
    mov  esi, OFFSET nameBuf
    call ValidName                  ; letters/space . - ' only, starts with letter
    cmp  eax, 1
    je   lsAge
    PrintErr msgBadName
    jmp  lsName

lsAge:                              ; ---- age ----
    PrintStr msgAge
    call ReadNumber                 ; CF = 1 if not a valid number
    jnc  lsAgeOk
    PrintErr msgInvalidNum
    jmp  lsAge
lsAgeOk:
    cmp  eax, MAX_AGE
    ja   lsAgeBad
    cmp  eax, 18
    jae  lsAgeGroup
    PrintErr msgUnderAge            ; failed login -> error beep
    LogMsg logUnderAge
    xor  eax, eax                   ; reject -> restart login
    jmp  lsExit
lsAgeBad:
    PrintErr msgBadAge
    jmp  lsAge
lsAgeGroup:
    call AgeToGroup                 ; EAX = age -> EAX = group 0..3
    mov  CurrentAgeGrp, eax         ; the age itself is now discarded

lsCnic:                             ; ---- CNIC ----
    PrintStr msgCnic
    mov  edx, OFFSET cnicBuf
    mov  ecx, READ_MAX
    call ReadString
    mov  esi, OFFSET cnicBuf
    call ValidCNIC                  ; EAX = 1 if exactly 13 digits
    cmp  eax, 1
    je   lsCnicOk
    PrintErr msgBadCnic
    jmp  lsCnic
lsCnicOk:
    mov  esi, OFFSET cnicBuf        ; remember who is logged in
    mov  edi, OFFSET CurrentUserCNIC
    call StrCopy
    call BuildFlags                 ; gender / age group / region -> CurrentFlags
    LogMsgCnic logLogin
    call Clrscr
    mov  eax, 1
lsExit:
    pop  edi
    pop  esi
    pop  edx
    pop  ecx
    ret
LoginScreen ENDP

; --------------------------------------------------------------------
;  AgeToGroup : EAX = age (18..120) -> EAX = 0:18-25 1:26-40 2:41-60 3:61+
; --------------------------------------------------------------------
AgeToGroup PROC
    cmp  eax, 25
    jbe  atg0
    cmp  eax, 40
    jbe  atg1
    cmp  eax, 60
    jbe  atg2
    mov  eax, 3
    ret
atg0:
    xor  eax, eax
    ret
atg1:
    mov  eax, 1
    ret
atg2:
    mov  eax, 2
    ret
AgeToGroup ENDP

; --------------------------------------------------------------------
;  BuildFlags : pack the logged-in voter's attributes into CurrentFlags
;    bit 1    gender  : last CNIC digit odd  -> male   (TEST + BTS)
;    bits 2-3 age grp : CurrentAgeGrp                  (AND + SHL + OR)
;    bits 4-7 region  : first CNIC digit 1..7, else 0  (AND + SHL + OR)
;    bit 0 (voted) is set later, by CastVote
; --------------------------------------------------------------------
BuildFlags PROC
    push eax
    push ebx
    xor  ebx, ebx                   ; EBX accumulates the flag bits

    movzx eax, BYTE PTR [CurrentUserCNIC + CNIC_DIGITS - 1]
    sub  eax, '0'
    test al, 1                      ; odd digit -> male
    jz   bfFemale
    bts  ebx, VF_MALE
bfFemale:
    mov  eax, CurrentAgeGrp
    and  eax, 3
    shl  eax, VF_AGE_SH
    or   ebx, eax

    movzx eax, BYTE PTR [CurrentUserCNIC]
    sub  eax, '0'
    cmp  eax, 7
    jbe  bfRegion
    xor  eax, eax                   ; 0, 8, 9 -> "other"
bfRegion:
    and  eax, 7
    shl  eax, VF_REG_SH
    or   ebx, eax

    mov  CurrentFlags, ebx
    pop  ebx
    pop  eax
    ret
BuildFlags ENDP

; --------------------------------------------------------------------
;  RoleMenu : choose User (1) or Admin (2)
; --------------------------------------------------------------------
RoleMenu PROC
rmTop:
    PrintStr msgRoleMenu
    call ReadNumber
    jc   rmInvalid
    cmp  eax, 1
    je   rmUser
    cmp  eax, 2
    je   rmAdmin
rmInvalid:
    PrintErr msgRoleInvalid
    call WaitMsg
    call Clrscr
    jmp  rmTop

rmUser:
    call UserMenu
    ret

rmAdmin:
    call AdminAuthentication        ; EAX = 1 granted / 0 denied
    cmp  eax, 0
    jne  rmAdminOk
    PrintErr msgDenied
    ret
rmAdminOk:
    call AdminMenu
    ret
RoleMenu ENDP

; --------------------------------------------------------------------
;  UserMenu
; --------------------------------------------------------------------
UserMenu PROC
umTop:
    call Clrscr
    SetColor CLR_LGREEN
    PrintStr artUser
    SetColor CLR_GRAY
    PrintStr menuUser
    call ReadNumber
    jnc  umGot
    PrintErr msgInvalidNum
    call WaitMsg
    jmp  umTop

umGot:
    cmp  eax, 1
    je   umShow
    cmp  eax, 2
    je   umVote
    cmp  eax, 3
    je   umCheck
    cmp  eax, 4
    je   umMain
    cmp  eax, 5
    je   umExit
    PrintErr msgInvalidChoice
    call WaitMsg
    jmp  umTop

umShow:
    call DisplayCandidates
    call WaitMsg
    jmp  umTop

umCheck:                            ; has MY cnic voted? (hash-table lookup)
    mov  esi, OFFSET CurrentUserCNIC
    call HasVoted
    cmp  eax, 1
    jne  umNotYet
    PrintClr CLR_YELLOW, msgYouHaveVoted
    call WaitMsg
    jmp  umTop
umNotYet:
    PrintClr CLR_GREEN, msgNotVotedYet
    call WaitMsg
    jmp  umTop

umVote:
    call CastVote
    ret                             ; log out after voting (as in the C version)

umMain:
    PrintClr CLR_GREEN, msgGoMain
    ret

umExit:
    PrintStr msgGoodbye
    call WaitMsg
    call QuitProgram
UserMenu ENDP

; --------------------------------------------------------------------
;  AdminMenu : options 1..ADMIN_N are dispatched through a jump table
; --------------------------------------------------------------------
AdminMenu PROC
amTop:
    call Clrscr
    SetColor CLR_YELLOW
    PrintStr artAdmin
    SetColor CLR_GRAY
    cmp  tamperFlag, 0
    je   amMenu
    PrintClr CLR_RED, msgTamperBanner
amMenu:
    PrintStr menuAdmin
    call ReadNumber
    jnc  amGot
    PrintErr msgInvalidNum
    call WaitMsg
    jmp  amTop

amGot:
    cmp  eax, 1
    jb   amBad
    cmp  eax, ADMIN_N + 2
    ja   amBad
    cmp  eax, ADMIN_N + 1
    je   amMain
    cmp  eax, ADMIN_N + 2
    je   amExit

    dec  eax                        ; option 1..12 -> table index 0..11
    call DWORD PTR adminTable[eax*4]
    call WaitMsg
    jmp  amTop

amBad:
    PrintErr msgInvalidChoice
    call WaitMsg
    jmp  amTop

amMain:
    PrintClr CLR_GREEN, msgGoMain
    ret

amExit:
    PrintStr msgSavedExit
    call WaitMsg
    call QuitProgram
AdminMenu ENDP

; --------------------------------------------------------------------
;  Password helpers
; --------------------------------------------------------------------

; ReadMasked : EDX = buffer, ECX = max chars -> EAX = chars typed
;   Reads keys with ReadChar (no echo) and prints '*' for each one.
;   Backspace removes the last character, Enter finishes.
ReadMasked PROC
    push ebx
    push esi
    mov  esi, edx                   ; ESI = buffer base
    xor  ebx, ebx                   ; EBX = length so far
rmaLoop:
    call ReadChar                   ; AL = key pressed
    cmp  al, 0Dh
    je   rmaEnter
    cmp  al, 8
    je   rmaBack
    cmp  al, 32                     ; ignore control / function keys
    jb   rmaLoop
    cmp  al, 126
    ja   rmaLoop
    cmp  ebx, ecx                   ; buffer full?
    jae  rmaLoop
    mov  [esi + ebx], al
    inc  ebx
    mov  al, '*'
    call WriteChar
    jmp  rmaLoop
rmaBack:
    test ebx, ebx
    jz   rmaLoop
    dec  ebx
    mov  al, 8                      ; erase the star on screen
    call WriteChar
    mov  al, ' '
    call WriteChar
    mov  al, 8
    call WriteChar
    jmp  rmaLoop
rmaEnter:
    mov  BYTE PTR [esi + ebx], 0
    call Crlf
    mov  eax, ebx
    pop  esi
    pop  ebx
    ret
ReadMasked ENDP

; HashStr : ESI = string -> EAX = 32-bit hash (ESI preserved)
;   per byte : h = ROL(h,5);  h = h XOR byte;  h = h + (h SHL 3)
;   final mix: h ^= h>>16;  h *= 45D9F3Bh;  h ^= h>>16
;   (a teaching hash - NOT cryptographically strong, no salt)
HashStr PROC
    push ebx
    push edx
    push esi
    mov  eax, HASH_SEED
hsLoop:
    movzx ebx, BYTE PTR [esi]
    test ebx, ebx
    jz   hsFinal
    rol  eax, 5
    xor  eax, ebx
    mov  edx, eax
    shl  edx, 3
    add  eax, edx
    inc  esi
    jmp  hsLoop
hsFinal:
    mov  edx, eax
    shr  edx, 16
    xor  eax, edx
    imul eax, 045D9F3Bh
    mov  edx, eax
    shr  edx, 16
    xor  eax, edx
    pop  esi
    pop  edx
    pop  ebx
    ret
HashStr ENDP

; CheckAdminPass : ESI = typed password -> EAX = 1 if its hash matches
CheckAdminPass PROC
    call HashStr
    cmp  eax, AdminHash
    jne  capNo
    mov  eax, 1
    ret
capNo:
    xor  eax, eax
    ret
CheckAdminPass ENDP

; WipePasswords : overwrite the three password buffers with zeros
WipePasswords PROC
    pushad
    cld
    xor  eax, eax
    mov  edi, OFFSET passBuf
    mov  ecx, SIZEOF passBuf
    rep  stosb
    mov  edi, OFFSET passBuf2
    mov  ecx, SIZEOF passBuf2
    rep  stosb
    mov  edi, OFFSET passBuf3
    mov  ecx, SIZEOF passBuf3
    rep  stosb
    popad
    ret
WipePasswords ENDP

; --------------------------------------------------------------------
;  AdminAuthentication : EAX = 1 granted / 0 denied
;  3 wrong passwords -> locked out for 1 hour
; --------------------------------------------------------------------
AdminAuthentication PROC
    push ebx
    push ecx
    push edx
    push esi
    push edi

    cmp  failedAttempts, 3          ; already locked?
    jb   aaStart
    call GetMseconds                ; ms since midnight
    sub  eax, lockoutStart          ; elapsed time
    jae  aaNoWrap
    add  eax, DAY_MS                ; midnight passed in between
aaNoWrap:
    cmp  eax, LOCK_MS
    jae  aaUnlock
    PrintErr msgLocked
    jmp  aaDenied
aaUnlock:
    mov  failedAttempts, 0

aaStart:
    mov  ebx, 3                     ; three tries
aaLoop:
    PrintStr msgAdminPass
    mov  edx, OFFSET passBuf
    mov  ecx, READ_MAX
    call ReadMasked                 ; shows ****** while typing
    mov  esi, OFFSET passBuf
    call CheckAdminPass             ; compares HASHES, not plaintext
    cmp  eax, 1
    je   aaGranted

    inc  failedAttempts
    SetColor CLR_RED
    PrintStr msgWrongPass
    mov  eax, 3
    sub  eax, failedAttempts
    call WriteDec
    call Crlf
    SetColor CLR_GRAY
    call BeepError                  ; failed login -> beep
    LogMsg logAdminFail

    cmp  failedAttempts, 3
    jb   aaNext
    call GetMseconds                ; start lockout timer
    mov  lockoutStart, eax
    LogMsg logAdminLock
    jmp  aaDenied
aaNext:
    dec  ebx
    jnz  aaLoop

aaDenied:
    call WipePasswords
    xor  eax, eax
    jmp  aaExit

aaGranted:
    call WipePasswords
    mov  failedAttempts, 0
    PrintClr CLR_GREEN, msgGranted
    LogMsg logAdminOk
    call WaitMsg
    mov  eax, 1
aaExit:
    pop  edi
    pop  esi
    pop  edx
    pop  ecx
    pop  ebx
    ret
AdminAuthentication ENDP

; --------------------------------------------------------------------
;  ChangePassword (admin) : only the new hash is stored
; --------------------------------------------------------------------
ChangePassword PROC
    pushad
    PrintStr msgOldPass
    mov  edx, OFFSET passBuf
    mov  ecx, READ_MAX
    call ReadMasked
    mov  esi, OFFSET passBuf
    call CheckAdminPass
    cmp  eax, 1
    je   cpOld
    PrintErr msgWrongOld
    LogMsg logPassFail
    jmp  cpDone
cpOld:
    PrintStr msgNewPass
    mov  edx, OFFSET passBuf2
    mov  ecx, READ_MAX
    call ReadMasked
    cmp  eax, PASS_MIN
    jae  cpLenOk
    PrintErr msgPassShort
    jmp  cpDone
cpLenOk:
    PrintStr msgConfirmPass
    mov  edx, OFFSET passBuf3
    mov  ecx, READ_MAX
    call ReadMasked
    mov  esi, OFFSET passBuf2
    mov  edi, OFFSET passBuf3
    call StrEqual
    cmp  eax, 1
    je   cpSame
    PrintErr msgPassNoMatch
    jmp  cpDone
cpSame:
    mov  esi, OFFSET passBuf2
    call HashStr
    mov  AdminHash, eax
    call SaveAdminHash
    PrintClr CLR_GREEN, msgPassChanged
    LogMsg logPassChanged
cpDone:
    call WipePasswords
    popad
    ret
ChangePassword ENDP

; --------------------------------------------------------------------
;  DisplayCandidates : numbered list of candidate names
; --------------------------------------------------------------------
DisplayCandidates PROC
    pushad
    SetColor CLR_LMAG
    PrintStr artCand
    SetColor CLR_GRAY

    mov  ecx, totalCandidates
    jecxz dcNone
    xor  ebx, ebx
dcLoop:
    lea  eax, [ebx + 1]             ; serial number
    call WriteDec
    mov  al, '.'
    call WriteChar
    mov  al, ' '
    call WriteChar
    mov  edx, candPtr[ebx*4]        ; cname is at offset 0
    call WriteString
    call Crlf
    inc  ebx
    loop dcLoop
    jmp  dcDone
dcNone:
    PrintStr msgNoCand
dcDone:
    popad
    ret
DisplayCandidates ENDP

; --------------------------------------------------------------------
;  CastVote : verify CNIC, check duplicates, count vote, save
; --------------------------------------------------------------------
CastVote PROC
    pushad

    cmp  totalCandidates, 0
    jne  cvHasCand
    PrintErr msgNoCand
    jmp  cvDone
cvHasCand:
    cmp  totalVoters, LENGTHOF voters
    jb   cvCapOk
    PrintErr msgRegFull
    jmp  cvDone

cvCapOk:
    PrintStr msgVerifyCnic          ; user must re-enter the CNIC used at login
    mov  edx, OFFSET cnicBuf
    mov  ecx, READ_MAX
    call ReadString
    mov  esi, OFFSET cnicBuf
    mov  edi, OFFSET CurrentUserCNIC
    call StrEqual
    cmp  eax, 1
    je   cvMatch
    PrintErr msgMismatch
    LogMsgCnic logCnicMismatch
    jmp  cvDone

cvMatch:
    mov  esi, OFFSET CurrentUserCNIC
    call HasVoted                   ; hash-table lookup: EAX = 1 if already voted
    cmp  eax, 1
    jne  cvNotVoted
    PrintErr msgAlreadyVoted
    LogMsgCnic logDupVote
    jmp  cvDone

cvNotVoted:
    call DisplayCandidates
    PrintStr msgEnterVote
    call ReadNumber
    jc   cvBadInput
    cmp  eax, 1
    jb   cvBadNum
    cmp  eax, totalCandidates
    ja   cvBadNum

    dec  eax                        ; convert to 0-based index
    mov  ebx, eax
    mov  esi, candPtr[ebx*4]
    inc  (Candidate PTR [esi]).votes ; count the vote

    SetColor CLR_GREEN
    PrintStr msgYouVoted
    mov  edx, esi                   ; cname at offset 0
    call WriteString
    PrintStr msgThanks
    SetColor CLR_GRAY

    mov  eax, totalVoters           ; EDI -> voters[totalVoters]
    imul edi, eax, SIZEOF Voter
    add  edi, OFFSET voters
    mov  esi, OFFSET CurrentUserCNIC
    call StrCopy                    ; store CNIC (field cnic, offset 0)
    mov  eax, CurrentFlags
    bts  eax, VF_VOTED              ; set the "voted" bit
    mov  (Voter PTR [edi]).flags, eax

    mov  eax, totalVoters
    call HashInsert                 ; index into the hash table
    inc  totalVoters
    call SaveCNICData
    call SaveElectionData
    call BeepOk                     ; success beep
    LogMsgCnic logVote              ; (who voted - NOT for whom)
    jmp  cvDone

cvBadInput:
    PrintErr msgInvalidNum
    jmp  cvDone
cvBadNum:
    PrintErr msgBadCand
cvDone:
    popad
    ret
CastVote ENDP

; --------------------------------------------------------------------
;  Hash table for the "already voted" check
;    slot = (CNIC as a number) MOD 101, computed digit by digit with DIV
;    (a 13-digit number does not fit in 32 bits, so Horner's rule is used)
;    collisions -> linear probing; table value = voter index + 1
; --------------------------------------------------------------------

; CnicHash : ESI = CNIC string -> EAX = slot 0..100
CnicHash PROC
    push ebx
    push ecx
    push edx
    push esi
    xor  eax, eax                   ; running remainder
    mov  ebx, HASH_SIZE
chLoop:
    movzx ecx, BYTE PTR [esi]
    test ecx, ecx
    jz   chDone
    sub  ecx, '0'
    imul eax, 10
    add  eax, ecx                   ; r*10 + digit
    xor  edx, edx
    div  ebx                        ; EDX = (r*10 + digit) mod 101
    mov  eax, edx
    inc  esi
    jmp  chLoop
chDone:
    pop  esi
    pop  edx
    pop  ecx
    pop  ebx
    ret
CnicHash ENDP

; HashInsert : EAX = voter index (already stored in voters[])
HashInsert PROC
    pushad
    mov  edx, eax                   ; keep the index
    imul esi, eax, SIZEOF Voter
    add  esi, OFFSET voters         ; ESI -> that voter's CNIC
    call CnicHash
    mov  ebx, eax                   ; first slot to try
hiProbe:
    cmp  hashTable[ebx*4], 0
    je   hiPlace
    inc  ebx                        ; collision -> next slot (wraps)
    cmp  ebx, LENGTHOF hashTable
    jb   hiProbe
    xor  ebx, ebx
    jmp  hiProbe
hiPlace:
    inc  edx                        ; store index + 1 so 0 can mean "empty"
    mov  hashTable[ebx*4], edx
    popad
    ret
HashInsert ENDP

; RebuildHash : recreate the table from voters[] (after loading the file)
RebuildHash PROC
    pushad
    cld
    xor  eax, eax
    mov  edi, OFFSET hashTable
    mov  ecx, LENGTHOF hashTable
    rep  stosd
    xor  ebx, ebx
rbLoop:
    cmp  ebx, totalVoters
    jae  rbDone
    mov  eax, ebx
    call HashInsert
    inc  ebx
    jmp  rbLoop
rbDone:
    popad
    ret
RebuildHash ENDP

; HasVoted : ESI = CNIC string -> EAX = 1 if already registered
HasVoted PROC
    push ebx
    push ecx
    push edx
    push edi
    call CnicHash
    mov  ebx, eax                   ; slot
    mov  ecx, LENGTHOF hashTable    ; never probe more than the table size
hvProbe:
    mov  eax, hashTable[ebx*4]
    test eax, eax
    jz   hvNo                       ; empty slot -> not in the table
    dec  eax                        ; voter index
    imul edi, eax, SIZEOF Voter
    add  edi, OFFSET voters
    call StrEqual                   ; ESI vs voters[i].cnic
    cmp  eax, 1
    je   hvYes
    inc  ebx
    cmp  ebx, LENGTHOF hashTable
    jb   hvNext
    xor  ebx, ebx
hvNext:
    loop hvProbe
hvNo:
    xor  eax, eax
    jmp  hvExit
hvYes:
    mov  eax, 1
hvExit:
    pop  edi
    pop  edx
    pop  ecx
    pop  ebx
    ret
HasVoted ENDP

; --------------------------------------------------------------------
;  Percentages
; --------------------------------------------------------------------

; CalcTenths : EAX = numerator, EDX = denominator -> EAX = percent * 10
;   (375 means 37.5%).  Uses the FPU: FILD, FIMUL, FIDIV, FISTP.
;   0 if the denominator is 0.  All other registers preserved.
CalcTenths PROC
    test edx, edx
    jnz  ctGo
    xor  eax, eax
    ret
ctGo:
    mov  fpuNum, eax
    mov  fpuDen, edx
    fild fpuNum                     ; ST0 = votes
    fimul k1000                     ; ST0 = votes * 1000
    fidiv fpuDen                    ; ST0 = votes * 1000 / total
    fistp fpuOut                    ; round to nearest, pop
    mov  eax, fpuOut
    ret
CalcTenths ENDP

; PrintTenths : EAX = percent*10 -> prints e.g. "37.5%"
PrintTenths PROC
    pushad
    mov  edi, OFFSET tmpBuf
    call AppendTenths
    mov  BYTE PTR [edi], '%'
    mov  BYTE PTR [edi + 1], 0
    mov  edx, OFFSET tmpBuf
    call WriteString
    popad
    ret
PrintTenths ENDP

; SumVotes : EAX = total votes held by the current candidates
SumVotes PROC
    push ebx
    push esi
    xor  eax, eax
    xor  ebx, ebx
svLoop:
    cmp  ebx, totalCandidates
    jae  svDone
    mov  esi, candPtr[ebx*4]
    add  eax, (Candidate PTR [esi]).votes
    inc  ebx
    jmp  svLoop
svDone:
    pop  esi
    pop  ebx
    ret
SumVotes ENDP

; PrintTurnout : "Voter turnout: N / MAX_VOTERS (xx.x%)"
PrintTurnout PROC
    pushad
    PrintStr msgTurnout
    mov  eax, totalVoters
    call WriteDec
    PrintStr msgSlash
    mov  eax, LENGTHOF voters
    call WriteDec
    PrintStr msgOpenParen
    mov  eax, totalVoters
    mov  edx, LENGTHOF voters
    call CalcTenths
    call PrintTenths
    PrintStr msgCloseNl
    popad
    ret
PrintTurnout ENDP

; --------------------------------------------------------------------
;  ShowResults : vote counts + percentages + current leader + turnout
; --------------------------------------------------------------------
ShowResults PROC
    pushad
    SetColor CLR_CYAN
    PrintStr artResults
    SetColor CLR_GRAY
    call PrintVoteCounts
    mov  esi, OFFSET msgLeading
    call PrintLeader
    call PrintTurnout
    popad
    ret
ShowResults ENDP

; --------------------------------------------------------------------
;  PrintVoteCounts : "Name: N votes (xx.x%)" for every candidate
; --------------------------------------------------------------------
PrintVoteCounts PROC
    pushad
    call SumVotes
    mov  edi, eax                   ; EDI = total votes cast
    mov  ecx, totalCandidates
    jecxz pvcDone
    xor  ebx, ebx
pvcLoop:
    mov  esi, candPtr[ebx*4]
    mov  edx, esi
    call WriteString
    PrintStr msgColon
    mov  eax, (Candidate PTR [esi]).votes
    call WriteDec
    PrintStr msgVotes
    PrintStr msgOpenParen
    mov  eax, (Candidate PTR [esi]).votes
    mov  edx, edi
    call CalcTenths                 ; FPU percentage
    call PrintTenths
    PrintStr msgCloseNl
    inc  ebx
    loop pvcLoop
pvcDone:
    popad
    ret
PrintVoteCounts ENDP

; --------------------------------------------------------------------
;  PrintLeader : ESI = prefix text ("Currently leading: " / "WINNER: ")
; --------------------------------------------------------------------
PrintLeader PROC
    pushad
    call FindLeadingCandidate       ; EAX = index, -1 none, -2 tie
    cmp  eax, -2
    je   plTie
    cmp  eax, -1
    je   plDone

    mov  ebx, eax
    mov  edx, esi                   ; prefix text
    call WriteString
    SetColor CLR_BROWN
    mov  esi, candPtr[ebx*4]
    mov  edx, esi
    call WriteString                ; leader's name
    SetColor CLR_GRAY
    PrintStr msgWith
    SetColor CLR_BROWN
    mov  eax, (Candidate PTR [esi]).votes
    call WriteDec                   ; leader's votes
    SetColor CLR_GRAY
    PrintStr msgVotesDot
    jmp  plDone

plTie:
    PrintClr CLR_BROWN, msgTie
plDone:
    popad
    ret
PrintLeader ENDP

; --------------------------------------------------------------------
;  FindLeadingCandidate : EAX = index of leader, -1 = no candidates,
;                         -2 = tie for first place
; --------------------------------------------------------------------
FindLeadingCandidate PROC
    push ebx
    push ecx
    push edx
    push esi
    push edi

    cmp  totalCandidates, 0
    jne  flStart
    mov  eax, -1
    jmp  flDone

flStart:
    mov  ebx, -1                    ; highest votes so far
    mov  esi, -1                    ; index of leader
    xor  ecx, ecx
flLoop1:                            ; step 1: find max votes + leader index
    cmp  ecx, totalCandidates
    jae  flStep2
    mov  edx, candPtr[ecx*4]
    mov  eax, (Candidate PTR [edx]).votes
    cmp  eax, ebx
    jle  flNext1
    mov  ebx, eax
    mov  esi, ecx
flNext1:
    inc  ecx
    jmp  flLoop1

flStep2:                            ; step 2: how many candidates share the max?
    xor  ecx, ecx
    xor  edi, edi
flLoop2:
    cmp  ecx, totalCandidates
    jae  flCheck
    mov  edx, candPtr[ecx*4]
    cmp  (Candidate PTR [edx]).votes, ebx
    jne  flNext2
    inc  edi
flNext2:
    inc  ecx
    jmp  flLoop2

flCheck:
    cmp  edi, 1
    jbe  flSingle
    mov  eax, -2                    ; tie
    jmp  flDone
flSingle:
    mov  eax, esi
flDone:
    pop  edi
    pop  esi
    pop  edx
    pop  ecx
    pop  ebx
    ret
FindLeadingCandidate ENDP

; --------------------------------------------------------------------
;  ShowGraph : colour-coded VERTICAL bar graph
;    Each candidate gets a column 8 characters wide and a colour from
;    barColors[].  Bars are drawn with coloured background spaces, so no
;    special characters are needed.  Height = votes * GRAPH_H / max (DIV).
; --------------------------------------------------------------------
ShowGraph PROC
    pushad
    SetColor CLR_CYAN
    PrintStr artGraph
    SetColor CLR_GRAY

    cmp  totalCandidates, 0
    jne  sgHas
    PrintStr msgNoCand
    jmp  sgDone

sgHas:                              ; ---- pass 1: highest vote count -> EDI
    xor  ebx, ebx
    xor  edi, edi
sgMax:
    cmp  ebx, totalCandidates
    jae  sgHeights
    mov  esi, candPtr[ebx*4]
    mov  eax, (Candidate PTR [esi]).votes
    cmp  eax, edi
    jbe  sgMaxNext
    mov  edi, eax
sgMaxNext:
    inc  ebx
    jmp  sgMax

sgHeights:                          ; ---- pass 2: bar heights
    xor  ebx, ebx
sgH:
    cmp  ebx, totalCandidates
    jae  sgDraw
    xor  eax, eax                   ; default height 0
    test edi, edi
    jz   sgStore                    ; nobody has votes yet
    mov  esi, candPtr[ebx*4]
    mov  eax, (Candidate PTR [esi]).votes
    imul eax, GRAPH_H
    xor  edx, edx
    div  edi                        ; votes * GRAPH_H / max
    test eax, eax
    jnz  sgStore
    cmp  (Candidate PTR [esi]).votes, 0
    je   sgStore
    mov  eax, 1                     ; any vote shows at least one row
sgStore:
    mov  graphH[ebx*4], eax
    inc  ebx
    jmp  sgH

sgDraw:                             ; ---- bars, top row first (ESI = row)
    mov  esi, GRAPH_H
sgRow:
    mov  ecx, 2
    call PadSpaces
    xor  ebx, ebx
sgCol:
    cmp  ebx, totalCandidates
    jae  sgRowEnd
    mov  ecx, 2
    call PadSpaces
    cmp  graphH[ebx*4], esi
    jb   sgBlank
    movzx eax, barColors[ebx]       ; bar = spaces with coloured BACKGROUND
    shl  eax, 4
    call SetTextColor
sgBlank:
    mov  ecx, 4
    call PadSpaces
    SetColor CLR_GRAY
    mov  ecx, 2
    call PadSpaces
    inc  ebx
    jmp  sgCol
sgRowEnd:
    call Crlf
    dec  esi
    jnz  sgRow

    mov  ecx, 2                     ; ---- baseline
    call PadSpaces
    mov  ecx, totalCandidates
    shl  ecx, 3                     ; 8 characters per column
    mov  al, '-'
    call RepeatChar
    call Crlf

    mov  ecx, 2                     ; ---- vote counts under the bars
    call PadSpaces
    xor  ebx, ebx
sgCnt:
    cmp  ebx, totalCandidates
    jae  sgCntEnd
    mov  esi, candPtr[ebx*4]
    mov  eax, (Candidate PTR [esi]).votes
    call PrintCell
    inc  ebx
    jmp  sgCnt
sgCntEnd:
    call Crlf

    mov  ecx, 2                     ; ---- candidate numbers in bar colour
    call PadSpaces
    xor  ebx, ebx
sgNum:
    cmp  ebx, totalCandidates
    jae  sgNumEnd
    movzx eax, barColors[ebx]
    call SetTextColor
    lea  eax, [ebx + 1]
    call PrintCell
    SetColor CLR_GRAY
    inc  ebx
    jmp  sgNum
sgNumEnd:
    call Crlf
    call Crlf

    xor  ebx, ebx                   ; ---- legend
sgLeg:
    cmp  ebx, totalCandidates
    jae  sgScale
    movzx eax, barColors[ebx]
    shl  eax, 4
    call SetTextColor
    mov  ecx, 2
    call PadSpaces
    SetColor CLR_GRAY
    mov  al, ' '
    call WriteChar
    lea  eax, [ebx + 1]
    call WriteDec
    mov  al, '.'
    call WriteChar
    mov  al, ' '
    call WriteChar
    mov  edx, candPtr[ebx*4]
    call WriteString
    call Crlf
    inc  ebx
    jmp  sgLeg

sgScale:
    PrintStr msgScale
    mov  eax, edi
    call WriteDec
    PrintStr msgScale2
sgDone:
    popad
    ret
ShowGraph ENDP

; RepeatChar : AL = character, ECX = count (all registers preserved)
RepeatChar PROC
    pushad
    jecxz rpDone
rpLoop:
    call WriteChar
    loop rpLoop
rpDone:
    popad
    ret
RepeatChar ENDP

; PadSpaces : ECX = number of spaces to print
PadSpaces PROC
    push eax
    mov  al, ' '
    call RepeatChar
    pop  eax
    ret
PadSpaces ENDP

; PrintCell : EAX = number, printed inside an 8-character cell
PrintCell PROC
    pushad
    mov  esi, eax
    mov  ecx, 3
    call PadSpaces
    mov  eax, esi
    call WriteDec
    mov  eax, esi                   ; count digits -> right padding
    mov  ebx, 10
    mov  ecx, 6
pcDig:
    dec  ecx
    xor  edx, edx
    div  ebx
    test eax, eax
    jnz  pcDig
    cmp  ecx, 0
    jle  pcEnd
    call PadSpaces
pcEnd:
    popad
    ret
PrintCell ENDP

; --------------------------------------------------------------------
;  AddCandidate (admin) : name goes into a freshly HeapAlloc'ed block
; --------------------------------------------------------------------
AddCandidate PROC
    pushad
    cmp  totalCandidates, LENGTHOF candPtr
    jb   acOk
    PrintErr msgMaxCand
    jmp  acDone
acOk:
    PrintStr msgNewName
    mov  edx, OFFSET nameBuf        ; read into a temporary buffer first
    mov  ecx, READ_MAX
    call ReadString
    mov  esi, OFFSET nameBuf
    call ValidName
    cmp  eax, 1
    je   acNameOk
    PrintErr msgBadName
    jmp  acDone
acNameOk:
    xor  ebx, ebx                   ; reject duplicate names (case-insensitive)
acDup:
    cmp  ebx, totalCandidates
    jae  acStore
    mov  edi, candPtr[ebx*4]
    mov  esi, OFFSET nameBuf
    call StrEqualI
    cmp  eax, 1
    je   acIsDup
    inc  ebx
    jmp  acDup
acIsDup:
    PrintErr msgDupCand
    jmp  acDone
acStore:
    mov  esi, OFFSET nameBuf
    call AppendCandidate            ; HeapAlloc + copy + register
    test eax, eax
    jnz  acAdded
    PrintErr msgAllocFail
    jmp  acDone
acAdded:
    PrintClr CLR_GREEN, msgAdded
    mov  esi, OFFSET logCandAdded
    mov  edx, OFFSET nameBuf
    call LogEvent
    call SaveElectionData           ; save immediately, not only on exit
acDone:
    popad
    ret
AddCandidate ENDP

; --------------------------------------------------------------------
;  RemoveCandidate (admin) : HeapFree the block, close the gap in candPtr
;  The votes it held go into removedVotes so the audit still balances.
; --------------------------------------------------------------------
RemoveCandidate PROC
    pushad
    cmp  totalCandidates, 0
    jne  rcHas
    PrintErr msgNoCand
    jmp  rcDone
rcHas:
    call DisplayCandidates
    PrintStr msgRemoveWhich
    call ReadNumber
    jc   rcInvalid
    cmp  eax, 1
    jb   rcInvalid
    cmp  eax, totalCandidates
    ja   rcInvalid

    dec  eax
    mov  ebx, eax                   ; EBX = index to remove
    mov  esi, candPtr[ebx*4]
    mov  eax, (Candidate PTR [esi]).votes
    add  removedVotes, eax          ; keep sum(votes)+removed = voters

    push esi                        ; log the name while it still exists
    mov  edx, esi
    mov  esi, OFFSET logCandRemoved
    call LogEvent
    pop  esi

    invoke HeapFree, hHeap, 0, esi  ; give the memory back
rcShift:
    mov  eax, totalCandidates
    dec  eax                        ; last valid index
    cmp  ebx, eax
    jae  rcShifted
    mov  eax, candPtr[ebx*4 + 4]    ; just move the POINTERS left
    mov  candPtr[ebx*4], eax
    inc  ebx
    jmp  rcShift
rcShifted:
    dec  totalCandidates
    mov  eax, totalCandidates
    mov  candPtr[eax*4], 0          ; clear the now-unused last slot
    PrintClr CLR_GREEN, msgRemoved
    call SaveElectionData           ; save immediately
    jmp  rcDone
rcInvalid:
    PrintErr msgInvalidCand
rcDone:
    popad
    ret
RemoveCandidate ENDP

; --------------------------------------------------------------------
;  DisplayVoters (admin) : list of CNICs that have voted
; --------------------------------------------------------------------
DisplayVoters PROC
    pushad
    SetColor CLR_LGREEN
    PrintStr artVoters
    SetColor CLR_GRAY

    mov  ecx, totalVoters
    jecxz dvNone
    xor  ebx, ebx
dvLoop:
    lea  eax, [ebx + 1]
    call WriteDec
    mov  al, '.'
    call WriteChar
    mov  al, ' '
    call WriteChar
    imul edx, ebx, SIZEOF Voter
    add  edx, OFFSET voters         ; cnic is the first field
    call WriteString
    call Crlf
    inc  ebx
    loop dvLoop
    jmp  dvDone
dvNone:
    PrintStr msgNoVoters
dvDone:
    popad
    ret
DisplayVoters ENDP

; --------------------------------------------------------------------
;  Turnout statistics (gender / age group / region)
; --------------------------------------------------------------------

; ComputeStats : count voters per gender, age group and region by
;   decoding each voter's flag DWORD (TEST, SHR, AND)
ComputeStats PROC
    pushad
    cld
    xor  eax, eax
    mov  edi, OFFSET genderCount
    mov  ecx, LENGTHOF genderCount
    rep  stosd
    mov  edi, OFFSET ageCount
    mov  ecx, LENGTHOF ageCount
    rep  stosd
    mov  edi, OFFSET regionCount
    mov  ecx, LENGTHOF regionCount
    rep  stosd

    xor  ebx, ebx
csLoop:
    cmp  ebx, totalVoters
    jae  csDone
    imul esi, ebx, SIZEOF Voter
    add  esi, OFFSET voters
    mov  edx, (Voter PTR [esi]).flags

    test edx, (1 SHL VF_MALE)       ; gender bit
    jz   csFemale
    inc  genderCount[TYPE genderCount]
    jmp  csAge
csFemale:
    inc  genderCount[0]
csAge:
    mov  eax, edx
    shr  eax, VF_AGE_SH
    and  eax, 3                     ; age group
    inc  ageCount[eax*4]
    mov  eax, edx
    shr  eax, VF_REG_SH
    and  eax, 7                     ; region
    inc  regionCount[eax*4]
    inc  ebx
    jmp  csLoop
csDone:
    popad
    ret
ComputeStats ENDP

; PrintStatRow : EDX = label string, EAX = count
;   prints "label: count (pct%)" with pct = count*100 / totalVoters (DIV)
PrintStatRow PROC
    pushad
    mov  esi, eax                   ; keep the count
    call WriteString                ; label (EDX)
    PrintStr msgColon
    mov  eax, esi
    call WriteDec
    PrintStr msgOpenParen
    mov  eax, esi
    imul eax, 100
    mov  ecx, totalVoters
    test ecx, ecx
    jz   psZero
    xor  edx, edx
    div  ecx                        ; integer percentage
    jmp  psShow
psZero:
    xor  eax, eax
psShow:
    call WriteDec
    PrintStr msgPctClose
    popad
    ret
PrintStatRow ENDP

; ShowStats (admin)
ShowStats PROC
    pushad
    call ComputeStats
    SetColor CLR_LCYAN
    PrintStr artStats
    SetColor CLR_GRAY
    call PrintTurnout
    call Crlf

    PrintStr msgGenderHdr
    mov  edx, OFFSET strFemale
    mov  eax, genderCount[0]
    call PrintStatRow
    mov  edx, OFFSET strMale
    mov  eax, genderCount[TYPE genderCount]
    call PrintStatRow

    PrintStr msgAgeHdr
    xor  ebx, ebx
ssAge:
    mov  edx, ageNames[ebx*4]
    mov  eax, ageCount[ebx*4]
    call PrintStatRow
    inc  ebx
    cmp  ebx, LENGTHOF ageCount
    jb   ssAge

    PrintStr msgRegHdr
    xor  ebx, ebx
ssReg:
    mov  edx, regionNames[ebx*4]
    mov  eax, regionCount[ebx*4]
    call PrintStatRow
    inc  ebx
    cmp  ebx, LENGTHOF regionCount
    jb   ssReg
    popad
    ret
ShowStats ENDP

; --------------------------------------------------------------------
;  Consistency audit
;    1) sum(candidate votes) + votes of removed candidates == totalVoters
;    2) every stored voter record has its "voted" bit set (BT)
;  EAX = 1 consistent / 0 tampered.  Also sets tamperFlag and logs failures.
; --------------------------------------------------------------------
CheckIntegrity PROC
    push ebx
    push ecx
    push edx
    mov  tamperFlag, 0
    call SumVotes
    mov  auditSum, eax
    add  eax, removedVotes
    cmp  eax, totalVoters
    jne  ciBad

    xor  ebx, ebx
ciFlags:
    cmp  ebx, totalVoters
    jae  ciOk
    imul edx, ebx, SIZEOF Voter
    add  edx, OFFSET voters
    mov  ecx, (Voter PTR [edx]).flags
    bt   ecx, VF_VOTED
    jnc  ciBad
    inc  ebx
    jmp  ciFlags
ciOk:
    mov  eax, 1
    jmp  ciExit
ciBad:
    mov  tamperFlag, 1
    LogMsg logTamper
    xor  eax, eax
ciExit:
    pop  edx
    pop  ecx
    pop  ebx
    ret
CheckIntegrity ENDP

; IntegrityReport (admin menu option)
IntegrityReport PROC
    pushad
    call CheckIntegrity
    SetColor CLR_LCYAN
    PrintStr artInteg
    SetColor CLR_GRAY
    PrintStr msgIntVotes
    mov  eax, auditSum
    call WriteDec
    call Crlf
    PrintStr msgIntRemoved
    mov  eax, removedVotes
    call WriteDec
    call Crlf
    PrintStr msgIntVoters
    mov  eax, totalVoters
    call WriteDec
    call Crlf
    cmp  tamperFlag, 0
    jne  irBad
    PrintClr CLR_GREEN, msgIntOk
    jmp  irDone
irBad:
    PrintErr msgIntBad
irDone:
    popad
    ret
IntegrityReport ENDP

; --------------------------------------------------------------------
;  EndVoting (admin) : password + confirmation + CNIC, then final
;  results are shown and the program terminates
; --------------------------------------------------------------------
EndVoting PROC
    pushad
    call Clrscr

    PrintStr msgAdminPass
    mov  edx, OFFSET passBuf
    mov  ecx, READ_MAX
    call ReadMasked
    mov  esi, OFFSET passBuf
    call CheckAdminPass
    mov  ebx, eax
    call WipePasswords
    cmp  ebx, 1
    je   evPassOk
    PrintErr msgPassMismatch
    jmp  evDone

evPassOk:
    PrintStr msgSure
    mov  edx, OFFSET inputBuf
    mov  ecx, READ_MAX
    call ReadString
    mov  esi, OFFSET inputBuf
    call ToLowerStr                 ; accept YES / Yes / y / Y ...
    mov  edi, OFFSET strYes
    call StrEqual
    cmp  eax, 1
    je   evConfirmed
    mov  edi, OFFSET strY
    call StrEqual
    cmp  eax, 1
    je   evConfirmed
    PrintErr msgDeclined
    jmp  evDone

evConfirmed:
    PrintStr msgVerifyAdmin
    mov  edx, OFFSET cnicBuf
    mov  ecx, READ_MAX
    call ReadString
    mov  esi, OFFSET cnicBuf
    mov  edi, OFFSET CurrentUserCNIC
    call StrEqual
    cmp  eax, 1
    je   evCnicOk
    PrintErr msgCnicMismatch
    jmp  evDone

evCnicOk:
    PrintClr CLR_GREEN, msgEnded
    LogMsg logEnded
    call WaitMsg
    call Clrscr

    mov  edx, OFFSET msgCounting
    call LoadingAnim
    call Clrscr

    SetColor CLR_LGREEN
    PrintStr artFinal
    SetColor CLR_GRAY
    call PrintVoteCounts
    mov  esi, OFFSET msgWinner
    call PrintLeader
    call PrintTurnout
    call Crlf
    call WaitMsg
    call QuitProgram                ; election is over -> save and end program

evDone:
    popad
    ret
EndVoting ENDP

; ====================================================================
;  FILE HANDLING  (binary files, Irvine32 file procedures)
; ====================================================================

; WriteBlock : EDX = buffer, ECX = bytes -> writes to fileHandle, CF = 1 on failure
WriteBlock PROC
    push ebx
    push edx
    push esi
    push edi
    push ecx
    mov  eax, fileHandle
    call WriteToFile                ; EAX = bytes actually written
    pop  ecx
    pop  edi
    pop  esi
    pop  edx
    pop  ebx
    cmp  eax, ecx
    jne  wbFail
    clc
    ret
wbFail:
    stc
    ret
WriteBlock ENDP

; ReadBlock : EDX = buffer, ECX = bytes <- reads from fileHandle, CF = 1 on failure
ReadBlock PROC
    push ebx
    push edx
    push esi
    push edi
    push ecx
    mov  eax, fileHandle
    call ReadFromFile               ; CF = error, EAX = bytes read
    pop  ecx                        ; POP does not change flags
    pop  edi
    pop  esi
    pop  edx
    pop  ebx
    jc   rbFail
    cmp  eax, ecx
    jne  rbFail
    clc
    ret
rbFail:
    stc
    ret
ReadBlock ENDP

; ---- election_data.dat : totalCandidates | removedVotes | N x Candidate ----
SaveElectionData PROC
    pushad
    mov  edx, OFFSET electionFile
    call CreateOutputFile
    cmp  eax, INVALID_HANDLE_VALUE
    je   sedFail
    mov  fileHandle, eax

    mov  edx, OFFSET totalCandidates
    mov  ecx, TYPE totalCandidates
    call WriteBlock
    jc   sedWriteFail
    mov  edx, OFFSET removedVotes
    mov  ecx, TYPE removedVotes
    call WriteBlock
    jc   sedWriteFail

    xor  ebx, ebx                   ; only the candidates that exist
sedLoop:
    cmp  ebx, totalCandidates
    jae  sedClose
    mov  edx, candPtr[ebx*4]
    mov  ecx, SIZEOF Candidate
    call WriteBlock
    jc   sedWriteFail
    inc  ebx
    jmp  sedLoop
sedClose:
    mov  eax, fileHandle
    call CloseFile
    jmp  sedDone
sedWriteFail:
    mov  eax, fileHandle
    call CloseFile
sedFail:
    PrintErr msgSaveErr
sedDone:
    popad
    ret
SaveElectionData ENDP

LoadElectionData PROC
    pushad
    mov  loadOk, 0
    mov  edx, OFFSET electionFile
    call OpenInputFile
    cmp  eax, INVALID_HANDLE_VALUE  ; no file yet -> first run
    je   ledDone
    mov  fileHandle, eax

    mov  edx, OFFSET totalCandidates
    mov  ecx, TYPE totalCandidates
    call ReadBlock
    jc   ledBad
    mov  edx, OFFSET removedVotes
    mov  ecx, TYPE removedVotes
    call ReadBlock
    jc   ledBad
    cmp  totalCandidates, LENGTHOF candPtr  ; sanity check against a corrupt file
    ja   ledBad

    xor  ebx, ebx
ledLoop:
    cmp  ebx, totalCandidates
    jae  ledRead
    invoke HeapAlloc, hHeap, HEAP_ZERO_MEMORY, SIZEOF Candidate
    test eax, eax
    jz   ledBad
    mov  candPtr[ebx*4], eax
    mov  edx, eax
    mov  ecx, SIZEOF Candidate
    call ReadBlock
    jc   ledBad
    inc  ebx
    jmp  ledLoop

ledRead:
    mov  eax, fileHandle
    call CloseFile
    xor  ebx, ebx
ledCheck:
    cmp  ebx, totalCandidates
    jae  ledOk
    mov  esi, candPtr[ebx*4]
    mov  BYTE PTR [esi + NAME_LEN - 1], 0   ; force a terminator in every name
    cmp  BYTE PTR [esi], 0                  ; a listed candidate needs a name
    je   ledCorrupt
    inc  ebx
    jmp  ledCheck
ledOk:
    mov  loadOk, 1
    jmp  ledDone
ledBad:
    mov  eax, fileHandle
    call CloseFile
ledCorrupt:
    call ClearElection              ; frees any blocks allocated so far
ledDone:
    popad
    ret
LoadElectionData ENDP

; ---- voted_cnic.dat : totalVoters | voters[] (CNIC + flags) ----
SaveCNICData PROC
    pushad
    mov  edx, OFFSET cnicFile
    call CreateOutputFile
    cmp  eax, INVALID_HANDLE_VALUE
    je   scdFail
    mov  fileHandle, eax

    mov  edx, OFFSET totalVoters
    mov  ecx, TYPE totalVoters
    call WriteBlock
    jc   scdWriteFail
    mov  edx, OFFSET voters
    mov  ecx, SIZEOF voters
    call WriteBlock
    jc   scdWriteFail
    mov  eax, fileHandle
    call CloseFile
    jmp  scdDone
scdWriteFail:
    mov  eax, fileHandle
    call CloseFile
scdFail:
    PrintErr msgSaveErr
scdDone:
    popad
    ret
SaveCNICData ENDP

LoadCNICData PROC
    pushad
    mov  edx, OFFSET cnicFile
    call OpenInputFile
    cmp  eax, INVALID_HANDLE_VALUE
    je   lcdDone
    mov  fileHandle, eax

    mov  edx, OFFSET totalVoters
    mov  ecx, TYPE totalVoters
    call ReadBlock
    jc   lcdBad
    mov  edx, OFFSET voters
    mov  ecx, SIZEOF voters
    call ReadBlock
    jc   lcdBad
    mov  eax, fileHandle
    call CloseFile

    cmp  totalVoters, LENGTHOF voters
    ja   lcdCorrupt
    xor  ebx, ebx
lcdTerm:
    cmp  ebx, LENGTHOF voters
    jae  lcdDone
    imul edi, ebx, SIZEOF Voter
    mov  BYTE PTR voters[edi + CNIC_LEN - 1], 0   ; force a terminator in every slot
    inc  ebx
    jmp  lcdTerm
lcdBad:
    mov  eax, fileHandle
    call CloseFile
lcdCorrupt:
    call ClearVoters
lcdDone:
    popad
    ret
LoadCNICData ENDP

; ---- admin_hash.dat : the 32-bit password hash (never the password) ----
SaveAdminHash PROC
    pushad
    mov  edx, OFFSET hashFile
    call CreateOutputFile
    cmp  eax, INVALID_HANDLE_VALUE
    je   sahFail
    mov  fileHandle, eax
    mov  edx, OFFSET AdminHash
    mov  ecx, TYPE AdminHash
    call WriteBlock
    mov  eax, fileHandle
    call CloseFile
    jmp  sahDone
sahFail:
    PrintErr msgSaveErr
sahDone:
    popad
    ret
SaveAdminHash ENDP

LoadAdminHash PROC
    pushad
    mov  edx, OFFSET hashFile
    call OpenInputFile
    cmp  eax, INVALID_HANDLE_VALUE  ; none saved -> keep the built-in default
    je   lahDone
    mov  fileHandle, eax
    mov  edx, OFFSET AdminHash
    mov  ecx, TYPE AdminHash
    call ReadBlock
    jnc  lahClose
    mov  AdminHash, DEFAULT_PASS_HASH
lahClose:
    mov  eax, fileHandle
    call CloseFile
lahDone:
    popad
    ret
LoadAdminHash ENDP

; ---- results.csv : opens in Excel / Notepad, easy to print ----
ExportResults PROC
    pushad
    mov  edx, OFFSET csvFile
    call CreateOutputFile
    cmp  eax, INVALID_HANDLE_VALUE
    je   exFail
    mov  fileHandle, eax

    call SumVotes
    mov  expTotal, eax

    mov  edi, OFFSET outBuf
    mov  esi, OFFSET csvHeader
    call AppendStr
    call EndLine

    xor  ebx, ebx
exLoop:
    cmp  ebx, totalCandidates
    jae  exSummary
    mov  esi, candPtr[ebx*4]
    call AppendStr                  ; name
    PutCh ','
    mov  eax, (Candidate PTR [esi]).votes
    call AppendDec
    PutCh ','
    mov  eax, (Candidate PTR [esi]).votes
    mov  edx, expTotal
    call CalcTenths
    call AppendTenths
    call EndLine
    inc  ebx
    jmp  exLoop

exSummary:
    mov  esi, OFFSET csvTotalVoters
    call AppendStr
    mov  eax, totalVoters
    call AppendDec
    call EndLine

    mov  esi, OFFSET csvWithdrawn
    call AppendStr
    mov  eax, removedVotes
    call AppendDec
    call EndLine

    mov  esi, OFFSET csvTurnout
    call AppendStr
    mov  eax, totalVoters
    mov  edx, LENGTHOF voters
    call CalcTenths
    call AppendTenths
    call EndLine

    mov  esi, OFFSET csvResult
    call AppendStr
    call FindLeadingCandidate
    cmp  eax, -2
    je   exTie
    cmp  eax, -1
    je   exNone
    mov  esi, candPtr[eax*4]
    jmp  exName
exTie:
    mov  esi, OFFSET csvTie
    jmp  exName
exNone:
    mov  esi, OFFSET csvNone
exName:
    call AppendStr
    call EndLine

    mov  eax, fileHandle
    call CloseFile
    PrintClr CLR_GREEN, msgExported
    LogMsg logExport
    jmp  exDone
exFail:
    PrintErr msgSaveErr
exDone:
    popad
    ret
ExportResults ENDP

; ====================================================================
;  AUDIT LOG  (append-only text file with timestamps)
; ====================================================================

; LogEvent : ESI = event text, EDX = extra string or 0
;   Appends  "[YYYY-MM-DD HH:MM:SS] event extra"  + CRLF to audit_log.txt
;   (time from GetLocalTime -> SYSTEMTIME).  Preserves all registers.
LogEvent PROC
    pushad
    mov  ebx, edx                   ; INVOKE may clobber EDX, so keep it here
    invoke GetLocalTime, ADDR sysTime

    mov  edi, OFFSET logBuf
    PutCh '['
    movzx eax, sysTime.wYear        ; year as two 2-digit halves (DIV by 100)
    mov  ecx, 100
    xor  edx, edx
    div  ecx
    push edx
    call Put2
    pop  eax
    call Put2
    PutCh '-'
    movzx eax, sysTime.wMonth
    call Put2
    PutCh '-'
    movzx eax, sysTime.wDay
    call Put2
    PutCh ' '
    movzx eax, sysTime.wHour
    call Put2
    PutCh ':'
    movzx eax, sysTime.wMinute
    call Put2
    PutCh ':'
    movzx eax, sysTime.wSecond
    call Put2
    PutCh ']'
    PutCh ' '

    call AppendStr                  ; event text (ESI)
    test ebx, ebx
    jz   leNoExtra
    PutCh ' '
    mov  esi, ebx
    call AppendStr                  ; extra text (e.g. CNIC / candidate name)
leNoExtra:
    PutCh 0Dh
    PutCh 0Ah
    mov  BYTE PTR [edi], 0
    mov  ecx, edi
    sub  ecx, OFFSET logBuf         ; length of the line
    mov  logLen, ecx

    invoke CreateFile, ADDR logFile, LOG_ACCESS, LOG_SHARE, 0, LOG_DISP, LOG_ATTR, 0
    cmp  eax, INVALID_HANDLE_VALUE
    je   leDone
    mov  logHandle, eax
    mov  edx, OFFSET logBuf
    mov  ecx, logLen
    call WriteToFile                ; EAX = handle (append-only, no seeking needed)
    mov  eax, logHandle
    call CloseFile
leDone:
    popad
    ret
LogEvent ENDP

; ShowAuditLog (admin) : dump audit_log.txt to the screen
ShowAuditLog PROC
    pushad
    SetColor CLR_LGREEN
    PrintStr artLog
    SetColor CLR_GRAY
    mov  edx, OFFSET logFile
    call OpenInputFile
    cmp  eax, INVALID_HANDLE_VALUE
    je   salNone
    mov  fileHandle, eax
salRead:
    mov  eax, fileHandle
    mov  edx, OFFSET readBuf
    mov  ecx, SIZEOF readBuf - 1
    call ReadFromFile
    jc   salEnd
    test eax, eax
    jz   salEnd
    mov  BYTE PTR readBuf[eax], 0
    mov  edx, OFFSET readBuf
    call WriteString
    jmp  salRead
salEnd:
    mov  eax, fileHandle
    call CloseFile
    jmp  salDone
salNone:
    PrintClr CLR_YELLOW, msgNoLog
salDone:
    popad
    ret
ShowAuditLog ENDP

; ====================================================================
;  SOUND AND ANIMATION
; ====================================================================
BeepOk PROC                         ; rising two-tone chirp
    pushad
    invoke Beep, 880, 90
    invoke Beep, 1320, 140
    popad
    ret
BeepOk ENDP

BeepError PROC                      ; short low buzz
    pushad
    invoke Beep, 300, 180
    popad
    ret
BeepError ENDP

; LoadingAnim : EDX = message.  Redraws one line with a carriage return
;   (0Dh) and pauses with Delay: "Message [#####.....] 25% /"
LoadingAnim PROC
    pushad
    mov  esi, edx
    xor  ebx, ebx                   ; frame 0..20
laLoop:
    mov  al, 0Dh                    ; back to the start of the line
    call WriteChar
    SetColor CLR_LCYAN
    mov  edx, esi
    call WriteString
    mov  al, '['
    call WriteChar
    mov  ecx, ebx
    mov  al, '#'
    call RepeatChar
    mov  ecx, 20
    sub  ecx, ebx
    mov  al, '.'
    call RepeatChar
    mov  al, ']'
    call WriteChar
    mov  al, ' '
    call WriteChar
    mov  eax, ebx
    imul eax, 5
    call WriteDec
    mov  al, '%'
    call WriteChar
    mov  al, ' '
    call WriteChar
    mov  eax, ebx
    and  eax, 3
    mov  al, spinner[eax]           ; | / - \
    call WriteChar
    SetColor CLR_GRAY
    mov  eax, 45
    call Delay                      ; 45 ms per frame
    inc  ebx
    cmp  ebx, 20
    jbe  laLoop
    call Crlf
    popad
    ret
LoadingAnim ENDP

; ====================================================================
;  HELPER PROCEDURES
; ====================================================================

; --------------------------------------------------------------------
;  ReadNumber : reads a line and converts it to an unsigned integer.
;  Returns  EAX = value, CF = 0 on success
;           EAX = 0,     CF = 1 if input is empty / not all digits / too long
;  (Own routine so invalid input never prints Irvine's built-in error.)
; --------------------------------------------------------------------
ReadNumber PROC
    push ebx
    push ecx
    push edx
    push esi

    mov  edx, OFFSET inputBuf
    mov  ecx, READ_MAX
    call ReadString                 ; EAX = number of characters typed
    cmp  eax, 0
    je   rnBad
    cmp  eax, 9                     ; max 9 digits -> fits in 32 bits
    ja   rnBad

    mov  ecx, eax
    mov  esi, OFFSET inputBuf
    xor  eax, eax
rnParse:
    movzx ebx, BYTE PTR [esi]
    cmp  bl, '0'
    jb   rnBad
    cmp  bl, '9'
    ja   rnBad
    sub  ebx, '0'
    imul eax, 10                    ; value = value*10 + digit
    add  eax, ebx
    inc  esi
    loop rnParse
    clc
    jmp  rnExit
rnBad:
    xor  eax, eax
    stc
rnExit:
    pop  esi                        ; POP does not change flags
    pop  edx
    pop  ecx
    pop  ebx
    ret
ReadNumber ENDP

; --------------------------------------------------------------------
;  ValidCNIC : ESI = string -> EAX = 1 if exactly 13 characters, all digits
; --------------------------------------------------------------------
ValidCNIC PROC
    push ecx
    push esi
    xor  ecx, ecx                   ; length counter
vcLoop:
    mov  al, [esi]
    cmp  al, 0
    je   vcEnd
    cmp  al, '0'
    jb   vcBad
    cmp  al, '9'
    ja   vcBad
    inc  ecx
    inc  esi
    jmp  vcLoop
vcEnd:
    cmp  ecx, CNIC_DIGITS
    jne  vcBad
    mov  eax, 1
    jmp  vcExit
vcBad:
    xor  eax, eax
vcExit:
    pop  esi
    pop  ecx
    ret
ValidCNIC ENDP

; --------------------------------------------------------------------
;  StrEqual : ESI, EDI = strings -> EAX = 1 if equal, 0 if different
; --------------------------------------------------------------------
StrEqual PROC
    push esi
    push edi
seLoop:
    mov  al, [esi]
    cmp  al, [edi]
    jne  seNo
    cmp  al, 0
    je   seYes
    inc  esi
    inc  edi
    jmp  seLoop
seYes:
    mov  eax, 1
    jmp  seExit
seNo:
    xor  eax, eax
seExit:
    pop  edi
    pop  esi
    ret
StrEqual ENDP

; --------------------------------------------------------------------
;  StrCopy : copy null-terminated string ESI -> EDI (includes the 0)
; --------------------------------------------------------------------
StrCopy PROC
    push esi
    push edi
scLoop:
    mov  al, [esi]
    mov  [edi], al
    inc  esi
    inc  edi
    cmp  al, 0
    jne  scLoop
    pop  edi
    pop  esi
    ret
StrCopy ENDP

; --------------------------------------------------------------------
;  AppendStr : append string ESI at [EDI]; EDI ends on the new terminator
;  (ESI preserved)
; --------------------------------------------------------------------
AppendStr PROC
    push esi
    push eax
asLoop:
    mov  al, [esi]
    test al, al
    jz   asDone
    mov  [edi], al
    inc  esi
    inc  edi
    jmp  asLoop
asDone:
    mov  BYTE PTR [edi], 0
    pop  eax
    pop  esi
    ret
AppendStr ENDP

; --------------------------------------------------------------------
;  AppendDec : EAX (unsigned) as decimal text at [EDI]; EDI advances
; --------------------------------------------------------------------
AppendDec PROC
    push eax
    push ebx
    push ecx
    push edx
    mov  ebx, 10
    xor  ecx, ecx
adDiv:
    xor  edx, edx
    div  ebx                        ; remainder = next digit (least first)
    push edx
    inc  ecx
    test eax, eax
    jnz  adDiv
adOut:
    pop  edx
    add  dl, '0'
    mov  [edi], dl
    inc  edi
    loop adOut
    mov  BYTE PTR [edi], 0
    pop  edx
    pop  ecx
    pop  ebx
    pop  eax
    ret
AppendDec ENDP

; AppendTenths : EAX = percent*10 -> "xx.x" text at [EDI]; EDI advances
AppendTenths PROC
    push eax
    push ebx
    push edx
    mov  ebx, 10
    xor  edx, edx
    div  ebx                        ; EAX = whole part, EDX = tenths digit
    push edx
    call AppendDec
    PutCh '.'
    pop  edx
    add  dl, '0'
    mov  [edi], dl
    inc  edi
    mov  BYTE PTR [edi], 0
    pop  edx
    pop  ebx
    pop  eax
    ret
AppendTenths ENDP

; Put2 : EAX (0..99) as exactly two digits at [EDI]; EDI += 2
Put2 PROC
    push eax
    push ebx
    push edx
    mov  ebx, 10
    xor  edx, edx
    div  ebx
    add  al, '0'
    mov  [edi], al
    add  dl, '0'
    mov  [edi + 1], dl
    add  edi, 2
    pop  edx
    pop  ebx
    pop  eax
    ret
Put2 ENDP

; EndLine : add CRLF to the line being built at outBuf, write it to the
;   open file (fileHandle) and rewind EDI to the start of outBuf
EndLine PROC
    mov  BYTE PTR [edi], 0Dh
    mov  BYTE PTR [edi + 1], 0Ah
    add  edi, 2
    push eax
    push ecx
    push edx
    mov  ecx, edi
    sub  ecx, OFFSET outBuf
    mov  edx, OFFSET outBuf
    call WriteBlock
    pop  edx
    pop  ecx
    pop  eax
    mov  edi, OFFSET outBuf
    ret
EndLine ENDP

; --------------------------------------------------------------------
;  ToLowerStr : convert string at ESI to lower case (in place)
; --------------------------------------------------------------------
ToLowerStr PROC
    push esi
tlLoop:
    mov  al, [esi]
    cmp  al, 0
    je   tlDone
    cmp  al, 'A'
    jb   tlNext
    cmp  al, 'Z'
    ja   tlNext
    add  al, 32                     ; 'A'(65) -> 'a'(97)
    mov  [esi], al
tlNext:
    inc  esi
    jmp  tlLoop
tlDone:
    pop  esi
    ret
ToLowerStr ENDP

; --------------------------------------------------------------------
;  ValidName : ESI = string -> EAX = 1 if acceptable name
;  Rules: first char is a letter; then letters, space, '.', '-', "'" only;
;         length 1..49 (fits the 50-byte slot with its terminator)
; --------------------------------------------------------------------
ValidName PROC
    push ecx
    push esi
    xor  ecx, ecx                   ; length counter
    mov  al, [esi]                  ; first character must be a letter
    cmp  al, 'A'
    jb   vnBad
    cmp  al, 'Z'
    jbe  vnLoop
    cmp  al, 'a'
    jb   vnBad
    cmp  al, 'z'
    ja   vnBad
vnLoop:
    mov  al, [esi]
    cmp  al, 0
    je   vnEnd
    cmp  al, ' '
    je   vnOk
    cmp  al, '.'
    je   vnOk
    cmp  al, '-'
    je   vnOk
    cmp  al, 39                     ; apostrophe
    je   vnOk
    cmp  al, 'A'
    jb   vnBad                      ; digits and other symbols land here
    cmp  al, 'Z'
    jbe  vnOk
    cmp  al, 'a'
    jb   vnBad
    cmp  al, 'z'
    ja   vnBad
vnOk:
    inc  ecx
    inc  esi
    jmp  vnLoop
vnEnd:
    cmp  ecx, NAME_LEN-1
    ja   vnBad
    mov  eax, 1
    jmp  vnExit
vnBad:
    xor  eax, eax
vnExit:
    pop  esi
    pop  ecx
    ret
ValidName ENDP

; --------------------------------------------------------------------
;  StrEqualI : ESI, EDI = strings -> EAX = 1 if equal ignoring case
; --------------------------------------------------------------------
StrEqualI PROC
    push ebx
    push esi
    push edi
seiLoop:
    mov  al, [esi]
    mov  bl, [edi]
    cmp  al, 'A'
    jb   seiL2
    cmp  al, 'Z'
    ja   seiL2
    add  al, 32
seiL2:
    cmp  bl, 'A'
    jb   seiCmp
    cmp  bl, 'Z'
    ja   seiCmp
    add  bl, 32
seiCmp:
    cmp  al, bl
    jne  seiNo
    cmp  al, 0
    je   seiYes
    inc  esi
    inc  edi
    jmp  seiLoop
seiYes:
    mov  eax, 1
    jmp  seiExit
seiNo:
    xor  eax, eax
seiExit:
    pop  edi
    pop  esi
    pop  ebx
    ret
StrEqualI ENDP

END main