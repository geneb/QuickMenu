'********** QuickMENU 3.2 - by Jay Munro
'QMRT runtime version
'Copyright (c) 1990 Jay Munro - revision 7/90  Version 3.2
'Distributed by Crescent Software
'For distribution rights please call Crescent Software

'QuickBASIC 4.5 version - load into the QB 4.5 editor with Pro.QLB
'Assembly Routines from QuickPak Professional
'
'EXE file compiled with BC7.1 PDS
'BC QMRT /O/S/FPA;  (floating point alternate library)
'LINK /EX /NOE QMENU.OBJ + NOLPT.OBJ + NOCOM.OBJ + NOGRAPH.OBJ + NOEVENT.OBJ + SMALLERR.OBJ + Logo.Obj,,NUL,PRO7.LIB;
'NOCOM.OBJ, NOLPT.OBJ, NOGRAPH.OBJ & SMALLERR.OBJ are
'contained in the BC 7.1 compiler libraries.
'LOGO.OBJ is provided with QMRT and was created with QuickScreen 3.X

'To compile & link with QB4.5
'BC QMRT /O/S;
'LINK /EX /NOE QMENU.OBJ + NOCOM.OBJ,,NUL,PRO.LIB;
'
'========================= Files used by Quick Menu =========================
'
' Trail - keeps track of last menu/choice selection up to 50 levels
' QM.Bat - created batch file that runs program choices
' *.QMU - menu files for each menu
' QMenu.QSL - title and help screens in QBase library format
'
' Command line switches    D - disables 1/1/80 date checking
'                          N - disables sound on errors or messages
'                          S - used internally only for DOS shell message
'============================= Declaration Dept =============================
'
'Declarations made to simplify calling syntax, since the subroutines may
'be called like BASIC keywords.  For example, "Inc A" calls the subroutine
'"Inc" to increment the value of A.  If a subprogram is not declared it
'would be called "CALL Inc (A)".  This is better, right?
'
DEFINT A-Z
DECLARE SUB Aprint0 (BYVAL A, B, C, D, E)    'Prints an array on screen
DECLARE SUB BarMenu (Item$(), Choice)        'Main Menu Engine
DECLARE SUB BlankScreen (X&)                 'Blanks screen after preset time
DECLARE SUB Build.Trail ()                   'Logs last menu & selection
DECLARE SUB BuildQmBatch ()                  'Builds QM.Bat file to run progs
DECLARE SUB CheckBye ()                      'Makes sure user wants to leave
DECLARE SUB CheckColor (Colr)                'Checks for illegal color combinations
DECLARE SUB SpltColr (Colr, FG, BG)
DECLARE SUB Default.Colr (X)                 'Sets Default colors for screen
DECLARE SUB Encrypt (S$, PW$)                'Encodes password
DECLARE FUNCTION Exist% (X$)                 'Checks for existance of file
DECLARE SUB Home.Base ()                     'Checks for existance of QMenu.EXE
DECLARE FUNCTION Homemenu% ()
DECLARE FUNCTION GetDir$ (Drive$)            'gets current default directory
DECLARE FUNCTION GetDrive% ()                'gets current default drive
DECLARE SUB Inst.Box ()                      'Prints commands available
DECLARE SUB LoadLogo ()                     'Loads Logo Screen if present
DECLARE FUNCTION MonType1 ()                 'Gets current monitor type
DECLARE SUB NoMenu ()
DECLARE SUB Password (X%, Y%)                'What else
DECLARE SUB QGetKey (A$, X%)                 'Waits and returns key
DECLARE SUB PromptBox ()
DECLARE SUB Qprint0 (X$, X)                  'Prints with color specified
DECLARE SUB ScrnSave0 (UR, UC, LR, LC, SEG Ary) 'Saves Screen
DECLARE SUB ScrnRest0 (UR, UC, LR, LC, SEG Ary) 'Restores screen
DECLARE SUB Screen.Char (X$)                 'Looks for interactive prompts
DECLARE SUB SetDrive (Drive$)                'sets a new default drive
DECLARE SUB Shell.Dos ()                     'Controls shell to DOS
DECLARE SUB Stuffbuf (Arg$)                  'Stuffs the keyboard buffer
DECLARE SUB TextIn (X%, T$, EditColr%)       'Main Text editor Engine
DECLARE SUB Tick.Toc (X)                     'Timer for waits
DECLARE SUB Timedate ()                      'Prints time & Date on screen
DECLARE FUNCTION Time2Num& (T$)              'Converts time to long int
DECLARE SUB Trail1 ()                        'Gets current menu title
DECLARE SUB Trail2 ()                        'Adds last menu title to stack
DECLARE SUB FillScrn0 (UR, UC, LR, LC, Cr, Char)   'Makes color window
DECLARE FUNCTION YN% (X%)                    'Yes no function
DECLARE SUB PaintBox0 (X, Y, Z, A, Colr)     'Paints area without changing it
DECLARE FUNCTION CapsLock% ()
DECLARE FUNCTION NumLock% ()

DATA Copyright 1990 (c) Jay Munro

'============================================================================
'                  Setup variables and check environment
'============================================================================
DIM SHARED FG, BG, Colr, Max, ExitCode, Num.Only, Caps.On, LastDate$, BlankTime%
DIM SHARED No.Choice, Max.Len, Num$(12), Item$(12, 22), Pswd$(10)
DIM SHARED Choice, Temp.Pswd$, Current.Menu$, ScrnArray(X), Top%
DIM SHARED Drive$, QMDir$, Thisfile$, PWCode%, SysPass$, Tune%
DIM SHARED Colr(9), Colr$(8), CL$(9), Shade%, Texture%, TxFil$

CONST DPW$ = "Crescent"
CT = 1                                  'Initialize count

Size% = 22
DIM SHARED Text$(Size%)                 'temporary edit/add variable for item$
Size% = 4600
DIM SHARED SCArray%(Size%)

 
DEF FNFG (Colr) = (Colr MOD 16)         'Parse out FG
DEF FNBG (Colr) = (Colr \ 16)           'Parse out BG

CLS
Default.Colr 0                          'Get Default color if no menu to start
Texture% = 176                          'Default texture character for background
BlankTime% = 0                          'Default to no screen blanking

Tune% = 6

Home.Base                               'Check for QMenu.EXE before continuing
Drive$ = CHR$(GetDrive%)                'Convert Drive to Drive Letter
QMDir$ = GetDir$(Drive$)                'Find Current Directory

IF QMDir$ = "" OR Drive$ = "" THEN      'a major disk error
   LOCATE 1, 1
   PRINT "Disk Error - Please correct and restart QuickMenu"
   END
END IF

'============================================================================
'  Get Preliminary information
'============================================================================
'Automatic Date checking
   

IF INSTR(COMMAND$, "D") THEN            'Skip the time and date prompt
	Thisfile$ = "QMRT " + COMMAND$
ELSE
	Thisfile$ = "QMRT " + COMMAND$  'Get the time and date prompt
	IF DATE$ = "01-01-1980" THEN
	     CLS
	     PRINT "Please set the date & Time or press enter to skip"
	     SHELL "Date"
	     SHELL "Time"
	END IF
END IF
IF INSTR(COMMAND$, "N") THEN Tune% = 99

'Check date against last time used

IF Exist%("Trail") THEN
   OPEN "Trail" FOR INPUT AS #1
     LINE INPUT #1, X$
     LINE INPUT #1, LastDate$
   CLOSE #1

   IF LastDate$ = DATE$ THEN
	Trail1
   ELSE
	KILL "Trail"
	LastDate$ = DATE$
	Build.Trail
	LoadLogo
   END IF
ELSE
    LastDate$ = DATE$
    Build.Trail
    LoadLogo
 END IF


'===========================================================================
Begin:
   
    ERASE Item$                         'Clear Item$ to start
    ERASE Pswd$                         'Clear password also
    IF NOT Exist%(Current.Menu$ + ".QMU") THEN 'No ?
	 IF Homemenu% THEN
	 NoMenu
       ELSE
	 Trail1
	 GOTO Start
       END IF
    END IF
   
    Password 0, 4

Start:
    ExitCode = 0                        'Start from scratch
    GOSUB Get.Menu                      'Load Item$() with menu choices
    TxFil$ = STRING$(3, Texture%)       'preload TxFil$ for Cap/Num area
    GOSUB Screen.One
'==========================================================================
'                     Sub - Routines start here
'===========================================================================
Menu.Display:                           '** Puts Menu On Screen **
   
    Inst.Box
    No.Choice = -1                      'Tell BarMenu to take choices
    Max.Len = 30
    ExitCode = 0                        'Reset ExitCode
    IF Choice = 0 THEN Choice = 1       'Eliminate 0 menu item
    BarMenu Num$(), Choice              'Selection area here

    IF ExitCode = 2 AND Homemenu THEN   'Escape to Exit
       CheckBye
       GOTO Start
    END IF

    SELECT CASE ExitCode
       CASE 2                           'Escape Key
	  Trail1
	  GOTO Start
       CASE 3                           'F3 Shell to DOS
	  Shell.Dos
	  GOTO Start
       CASE 5                           'F5 Key - prompted exit
	  CheckBye
	   GOTO Start
       CASE 8                           'Alt-F5 - fast exit
	  BuildQmBatch
       CASE 9                           'restarts to main menu
	  IF Exist%("Trail") THEN
		KILL "Trail"
		Build.Trail
		Trail1
		GOTO Start
	   ELSE
		GOTO Menu.Display
	   END IF
      
       CASE ELSE
    END SELECT

    Password X%, 1
    IF NOT X% THEN
       CALL Chime(Tune%)
       GOTO Menu.Display
    END IF

    IF Item$(Choice, 22) = "M" THEN     'The item selected was a menu
       CT = Choice                      'Set CT to be remembered
       GOTO Menu.Change                 'Fetch new menu
    END IF

    BuildQmBatch                        'Regular selection - Do it
    GOTO Start

'===========================================================================
Screen.One:                             'Setup Screen
   
    FillScrn0 1, 1, 25, 80, Colr(2), Texture%    'clear screen
   
    LOCATE 1, 34, 0
    Qprint0 CHR$(17) + "           " + CHR$(16), -1  'Colr(2)
    LOCATE 1, 36
    Qprint0 "QuickMenu", Colr(2)        'Our Logo
    GOSUB LogoBox                       'Display Menu Title
   
    PaintBox0 4, 5, 5, 12, Shade%
    FillScrn0 3, 4, 4, 11, Colr(5), 32
    PaintBox0 4, 69, 5, 78, Shade%      'background shadow for date
    FillScrn0 3, 68, 4, 77, Colr(5), 32
   
    LOCATE 4, 6, 0
    Qprint0 "TIME", -1
    LOCATE , 71, 0
    Qprint0 "DATE", -1
  
    RETURN
'===========================================================================

Menu.Change:
    Last.Menu$ = Current.Menu$          'Set Menu we're leaving
    Trail2                              'Log Change on Trail
    Current.Menu$ = Item$(Choice, 1)    'Pick up new title
    Choice = 1                          'Reset Choice
    GOTO Begin                          'Go get menu

'============================== Start-up menu ===============================

Get.Menu:                               'Loads Array for current menu choices
    CheckFlag% = 0
    IF NOT Exist%(Current.Menu$ + ".QMU") THEN
      IF NOT Homemenu% THEN
	Trail1
	GOTO Start
      ELSE
	NoMenu
      END IF
    END IF
    ERASE Item$                         'Clear Item$ to start
    ERASE Pswd$
    OPEN Current.Menu$ + ".QMU" FOR INPUT AS #1
	 LINE INPUT #1, Item$(0, 0)     'Menu Title
	 LINE INPUT #1, Item$(0, 1)     'Number of Items
	    IF Item$(0, 1) = "" THEN    'If no items then let's
	       CLOSE #1                 '  build a menu
	       IF Homemenu% THEN NoMenu
	       Trail1
	       GOTO Start
	    END IF

	 LINE INPUT #1, Mix$            'Background Texture
	
	 FOR X = 1 TO 8                 'Get the colors
	     LINE INPUT #1, Colr$(X)
	     Colr(X) = VAL(Colr$(X))
	     IF Colr(X) = 0 THEN CheckFlag% = -1
	     CheckColor Colr(X)
	 NEXT X
	  
	 FOR CT = 1 TO VAL(Item$(0, 1))         'Get all the commands
	     LINE INPUT #1, Item$(CT, 22)       '  for each menu item
	     FOR X = 0 TO 20
		 LINE INPUT #1, Item$(CT, X)
		 IF Item$(CT, X) = "" THEN EXIT FOR
	     NEXT X
	 NEXT CT
   
	 Position% = SEEK(1)
	 CLOSE #1

    OPEN Current.Menu$ + ".QMU" FOR BINARY AS #1 'Get passwords
	 X$ = SPACE$(1)
	 GET #1, Position, X$
	 Position% = SEEK(1)
	 Pswd$(0) = SPACE$(8)
	 GET #1, Position, Pswd$(0)
						
    FOR X = 1 TO CT                             'Set up name only array
	Pswd$(X) = SPACE$(8)
	GET #1, Position% + (X * 8), Pswd$(X)
	Num$(X) = STR$(X) + "  " + Item$(X, 0)
    NEXT X
    
    CLOSE #1                                    'Get exit password
   
    IF INSTR(Mix$, "-") = 0 THEN                'old pw menu had date here
       IF INSTR(Mix$, "*") THEN                 'new ones have *
	  X% = INSTR(Mix$, "*")                 'format is 176*60=8
	  Texture% = VAL(Mix$)                  '           |   | |
	  BlankTime% = VAL(MID$(Mix$, X% + 1))  '   texture/    | |
	  X% = INSTR(Mix$, "=")                 ' blanktime  /  |
	  IF X% THEN
	     Shade% = VAL(MID$(Mix$, X% + 1))   ' shadow color /
	  ELSE
	     Shade% = 8
	  END IF
       ELSE
	  Texture% = VAL(LTRIM$(Mix$))
	  BlankTime% = 0
	  Shade% = 8
       END IF
    END IF
    
    Password 3, 4
    IF CheckFlag% THEN Default.Colr 0               'if any color was 0 set defaults
    RETURN                                          ' used for demos etc...
						    ' so menu is correct on any monitor
LogoBox:
   
    IF Item$(0, 0) = "" THEN Item$(0, 0) = "Your Title Here"

    Wth = LEN(Item$(0, 0))              'Box around Title
    UR = 3
    UC = (39 - (Wth / 2))
    LR = 5
    LC = UC + Wth + 3
   
    FillScrn0 UR, 15, UR + 4, 57, Colr(2), Texture%
    PaintBox0 UR + 1, UC + 1, LR + 1, LC + 1, Shade%   'Clear Box area to title color
    FillScrn0 UR, UC, LR, LC, Colr(1), 32   'Clear Box area to title color

    LOCATE 4, UC + 2
    Qprint0 Item$(0, 0), Colr(1)         'Put up new title

RETURN
   
END
'=============================== End of Main Program ========================

'-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-==-=-=-=-=-=-=-
'
'This program is dedicated to my wife Kathryn and young-uns Katie & Jayson
'who have put up with the late nights, long hours and temper tantrums when
'I ran into bugs.    Thanks
'                     Jay

SUB BarMenu (Num$(), Choice) STATIC          'Item$() has one dimension
    ExitCode = 0                             'Choice is the value returned
    Left.Marg = 24

'----- determine how many choices to display, and where to put the menu

    Max.Num = VAL(Item$(0, 1))
    Top = 11 - (Max.Num \ 2)                 'locates menu in center of screen

'----- draw border and display items on the screen

Border:
    PaintBox0 Top + 1, (Left.Marg - 1), (Top + Max.Num + 3), (Left.Marg + Max.Len + 6), Shade%
    FillScrn0 Top, (Left.Marg - 2), (Top + Max.Num + 2), (Left.Marg + Max.Len + 5), Colr(3), 32

    LOCATE Top + 1, Left.Marg - 1
    Aprint0 VARPTR(Num$(1)), Max.Num, 1, Max.Len + 4, Colr(3)
  

    LOCATE (Top + Max.Num + 2), Left.Marg + 1
    Qprint0 "Use " + CHR$(24) + " or " + CHR$(25) + " and <Enter> to Select", Colr(3)
  
'----- make inverse cursor bar over Items

Get.Loop:
    Clr = Colr(7)
    GOSUB Display                       'make inverse bar on item

BGet.Key:
    QGetKey X$, -1
   
    SELECT CASE X$
       CASE CHR$(13)                    'Enter key
	  EXIT SUB
       CASE CHR$(27)                    'Escape Key
	  ExitCode = 2
	  EXIT SUB
       CASE CHR$(0) + "="               'F3 Shell
	  ExitCode = 3
	  EXIT SUB
       CASE CHR$(0) + "?"               'Quit F5
	  ExitCode = 5
	  EXIT SUB
       CASE CHR$(0) + "l"               'Quick Quit Alt(f5)
	  IF SysPass$ <> DPW$ THEN ExitCode = 5 ELSE ExitCode = 8
	  EXIT SUB
       CASE CHR$(0) + "2"               'Alt - M  return to main menu
	  ExitCode = 9
	  EXIT SUB
       CASE ELSE
    END SELECT

    Clr = Colr(3)
    GOSUB Display                       'restore old item
    X = VAL(X$)                         'set X to new item

    IF X > 0 AND X <= Max.Num THEN      'Numeric Key used for selection
       Choice = VAL(X$)
       Clr = Colr%(7)
       GOSUB Display
       EXIT SUB
    END IF

    SELECT CASE X$                              'Up arrow
       CASE CHR$(0) + "H"
	  Choice = Choice - 1
	  IF Choice < 1 THEN Choice = Max.Num
       CASE CHR$(0) + "P", CHR$(32)             'Down Arrow, Space Bar
	  Choice = Choice + 1
	  IF Choice > Max.Num THEN Choice = 1
       CASE CHR$(0) + "G"                       'Home key
	  Choice = 1
       CASE CHR$(0) + "O"                       'End Key
	  Choice = Max.Num
       CASE ELSE
    END SELECT

    GOTO Get.Loop                               'get again


'----- Mark/Unmark cursor bar Items

Display:

    LOCATE Top + Choice, Left.Marg - 1          'position cursor
						'pad with blanks if needed
    Qprint0 Num$(Choice) + SPACE$(Max.Len + 6 - LEN(Num$(Choice))), Clr
    RETURN

END SUB

				      'blanks screen after predetermined time
SUB BlankScreen (CheckTime&) STATIC
     
  IF Time2Num&(TIME$) - CheckTime& < BlankTime% THEN EXIT SUB 'not over time limit yet
    
       CursorRow% = CSRLIN            'save cursor position
       CursorCol% = POS(1)
       CALL ScrnSave0(1, 1, 25, 80, SEG SCArray%(0))  'save screen
       FillScrn0 1, 1, 25, 80, 7, 32
       Flag% = -1
       WHILE INKEY$ = ""
	 
	  IF Time2Num&(TIME$) <> LastTime& THEN
	     IF Flag% THEN
		FillScrn0 1, 1, 25, 80, 7, 32
		LOCATE RND(TIMER) * 23 + 1, RND(TIMER) * 70 + 1
		Qprint0 "QuickMenu", -1
		Flag% = 0
		LastTime& = Time2Num&(TIME$)
	     END IF
	  ELSE
	     Flag% = -1
	  END IF
       WEND
       CheckTime& = Time2Num&(TIME$)
       LOCATE CursorRow%, CursorCol%
       CALL ScrnRest0(1, 1, 25, 80, SEG SCArray%(0))

END SUB

SUB Build.Trail STATIC                  'Default Trail file
							 
    IF Exist("Trail") THEN EXIT SUB

    IF Choice < 1 THEN Choice = 1
    OPEN "Trail" FOR OUTPUT AS #2
	 PRINT #2, Thisfile$            'This menu name for future use
	 PRINT #2, DATE$                'Date Stamp
	 PRINT #2, "MENU"               'Default first menu
	 PRINT #2, STR$(Choice)         'Last Choice
    CLOSE #2
    Current.Menu$ = "MENU"
    LastDate$ = DATE$
END SUB

SUB BuildQmBatch STATIC                'Builds Batch file to do work
   
    NoReturn = 0

    RunFile$ = "QM" + CHR$(13)
    Trail2
	 
    SELECT CASE ExitCode                'Check for exit condition
       CASE 2, 5, 8                     'Escape , F5 , Alt F5
	  GOTO Bye                      'forget the batch file
       CASE ELSE
    END SELECT

    OPEN "QM.Bat" FOR OUTPUT AS #1      'Ok here we go
	 PRINT #1, "Echo Off"           'Boiler Plate stuff to
	 PRINT #1, "CLS"                'Picks up here when selection
	 FOR X = 1 TO 20                'Loads up commands
	     IF Item$(Choice, X) = "" THEN EXIT FOR
	     Screen.Char Item$(Choice, X)    'Check for message or
					     '  input characters
	     SELECT CASE ExitCode
		CASE 1                       'Print whole command (normal)
		   PRINT #1, Item$(Choice, X)
		CASE 2                       'Escape - Bagout last minute
		   CLOSE #1
		   Trail1
		   EXIT SUB                  'Goto Start
		CASE 3                       'Print Just User Input
		   PRINT #1, LEFT$(Item$(Choice, X), (LEN(Item$(Choice, X)) - 1));
		CASE 4                      'Character detected for
		   NoReturn% = -1           'skipping return stuff
		CASE ELSE
	     END SELECT

	 NEXT X
	 IF NoReturn THEN GOTO DontReturn

Finish:                                 'Return back to This menu
	 PRINT #1, Drive$ + ":"         'Make sure its the current drive
	 PRINT #1, "CD" + QMDir$        'and the current directory
	 PRINT #1, "Echo Off"           'Try to keep commands off screen
	 PRINT #1, "CLS"                'Clean sweep
	 PRINT #1, Thisfile$;           'Return to this prog, DON'T FORGET
					'  the Semi-Colon

DontReturn:                             'Jump to here to skip return stuff
    CLOSE #1
    COLOR 0, 0                      'Black on black for cursor
    Stuffbuf RunFile$               'The Main Event
    CLS
    END                             'this runs the batch file

Bye:                                'Exit to DOS
    CHDIR Drive$ + ":\"             'goto Root Dir
    COLOR 7, 0
    CLS
    END
   
END SUB

SUB CheckBye
   
    ScrnSave0 11, 29, 14, 50, SEG SCArray%(4000)
    PaintBox0 12, 30, 15, 51, Shade%
    FillScrn0 11, 29, 14, 50, Colr(6), 32
    
    LOCATE 12, 34
    Qprint0 "Exit To DOS?", -1

    IF SysPass$ = DPW$ THEN LOCATE 13, 39: Qprint0 "Y/N", -1
    CALL Chime(Tune%)

    IF SysPass$ = DPW$ THEN                'If System password is default
	IF YN%(-1) THEN
	  ExitCode = 8
	  BuildQmBatch
       ELSE
	  EXIT SUB
       END IF
    END IF
   
    PWCode% = 1
    Password PWCode%, 4                    'If Syspass has been done
					   'then get it before leaving
    IF PWCode% THEN
       ExitCode = 8
       BuildQmBatch
    END IF

    ScrnRest0 11, 29, 14, 50, SEG SCArray%(4000)

END SUB

DEFSNG A-Z
SUB CheckColor (Clr%)                 'checks for legal colors and set default
				      ' colors to Black and White
    IF Monitor% = 0 AND FNFG%(Clr%) = FNBG%(Clr%) THEN Clr% = 7: EXIT SUB
    IF Clr% = 0 OR Clr% = 8 THEN Clr% = 7             'If B+W check for illegal
						      ' combinations.
END SUB

DEFINT A-Z
SUB Default.Colr (Y)            'Sets beginning color according to monitor
    

    Mon = MonType1%              'Get monitor type
    IF Y THEN Mon = Y * 99      'Check for over-ride on defaults
    Shade% = 8                  'Default color for shadows

    SELECT CASE Mon
       CASE -1, 99              'EGA mono, Herc,Mono,VGA mono
	  Colr(1) = 112
	  Colr(2) = 7
	  Colr(3) = 112
	  Colr(4) = 112
	  Colr(5) = 112
	  Colr(6) = 15
	  Colr(7) = 15
	  Colr(8) = 7
	  EXIT SUB
       CASE ELSE
	  Colr(1) = 95
	  Colr(2) = 49
	  Colr(3) = 27
	  Colr(4) = 96
	  Colr(5) = 32
	  Colr(6) = 78
	  Colr(7) = 33
	  Colr(8) = 30
    END SELECT
	 
END SUB

SUB Home.Base STATIC                    'Alerts user if QuickMenu was started
					'the wrong subdirectory
    IF Exist%("QMRT.EXE") THEN EXIT SUB

    FillScrn0 11, 12, 14, 68, Colr(6), 32
    LOCATE 12, 13
    Qprint0 "Please start QuickMenu Runtime from its home directory.", Colr(6)
    LOCATE 13, 25
    Qprint0 "Press any key to return to DOS", Colr(6)
    CALL Chime(Tune%)
    QGetKey A$, 0
    CLS
    END

END SUB

DEFSNG A-Z
FUNCTION Homemenu%
IF Current.Menu$ = "MENU" THEN Homemenu% = -1 ELSE Homemenu% = 0
END FUNCTION

DEFINT A-Z
SUB Inst.Box STATIC
    
    FillScrn0 21, 2, 21, 79, Colr(2), Texture%            'clear prompt line

    PromptBox

    LOCATE 23, 10
    Qprint0 "<F3> Shell" + SPACE$(38) + "<F5> Exit to DOS", Colr(4)
	
    IF NOT Homemenu THEN                                'Not Main Menu
       LOCATE 21, 24                                    'Show how to get back
       Qprint0 CHR$(17) + " Press <ESC> for Previous Menu " + CHR$(16), Colr(2)
    END IF

END SUB

SUB LoadLogo

Getlogo:
    CLS
    IF MonType1% THEN X = 3 ELSE X = 0
    CALL Logo(X)
    QGetKey A$, 0
    CLS

END SUB

DEFSNG A-Z
FUNCTION MonType1%
   
    DEF SEG = 0
    IF PEEK(&H463) = &HB4 THEN
       MonType1% = -1                     'Monochrome
    ELSE
       MonType1% = 0                      'Color
    END IF

END FUNCTION

SUB NoMenu
       CALL Chime(Tune%)
       LOCATE 11, 10
       Qprint0 "Please build all with QuickMenu before using runtime version", Colr%(4)
       LOCATE 12, 25
       Qprint0 "press any key to return to DOS", Colr%(4)
       QGetKey A$, 0
       CLS
       END
END SUB

DEFINT A-Z
SUB Password (PWCode%, Level%)
   
    IF Level% = 1 AND Pswd$(Choice) = DPW$ THEN 'No PW exists
       PWCode% = -1                             'Give the okey dokey
       EXIT SUB
    END IF

   ScrnSave0 1, 1, 25, 80, SEG SCArray%(2000)

    SELECT CASE Level%
       CASE 1                                   'Check password
	  GOSUB CheckState
	  PromptBox
	  GOTO Check.Password
       CASE 4
	  GOTO System.Password
       CASE ELSE
    END SELECT
   
Check.Password:
    PWCode% = 0                                 'Default = wrong pw
    GOSUB AskPassword
    GOTO CheckPW

AskPassword:
    Pswd$ = ""                                  'Initialize password var
   
    PaintBox0 21, 28, 23, 54, Shade%            'Shadow
    FillScrn0 20, 27, 22, 53, Colr(2), 32        'make a box
   
    LOCATE 20, 29
    Qprint0 "Enter Password", Colr(2)
    LOCATE 22, 29
    Qprint0 "Press <ESC> to Re-Enter", Colr(2)
    
    LOCATE 21, 35
    Qprint0 "¯        ®", Colr(2)
    FOR X = 1 TO 8

GetPassword:                                    'get a character
    QGetKey A$, -1                                ' and build the password
    IF A$ = CHR$(0) + CHR$(75) THEN A$ = CHR$(8)
    IF LEN(A$) > 1 GOTO GetPassword             'we are using this
    IF LEN(Pswd$) = 0 AND A$ = CHR$(13) THEN    ' since we don't want to
       PWCode% = 0                              ' show what is typed
       GOTO Exit.Password
    END IF
    
    SELECT CASE A$
       CASE CHR$(27)                            'Esc pressed
	  PWCode% = 0
	  GOTO Exit.Password
       CASE CHR$(13)                            'Enter pressed
	  EXIT FOR
       CASE CHR$(8)                             'Backspace
	  X = X - 1                             'Dec character count
	  IF X < 1 THEN X = 1                   'Check for 0 for no errors
	  Pswd$ = LEFT$(Pswd$, X - 1)           'Erase Last character from PSWD$
	  LOCATE 21, 35 + X                     'Print space over last char
	  Qprint0 " ", Colr(2)
	  GOTO GetPassword                      'Leave
       CASE ELSE
    END SELECT

    Pswd$ = Pswd$ + A$                       'build password var
    LOCATE 21, 35 + X                        ' but just print
    Qprint0 "*", Colr(2)                     ' *'s for prying eyes
    NEXT X
   
    Scrt$ = "Copyrite"                       'Here's our default
    Encrypt Scrt$, Pswd$                     'encrypte it
    RETURN

CheckPW:
    IF Scrt$ = Pswd$(Choice) THEN PWCode% = -1   'Check out users response
    GOTO Exit.Password
		

System.Password:
GetSysPW:
   
    OPEN "MENU.QMU" FOR BINARY AS #1             'file i/o here
       LN% = LOF(1)                              'get end of file
       SysPass$ = SPACE$(8)                      'system password is
       GET #1, LN% - 7, SysPass$                 'last password on stack
    CLOSE #1

    IF SysPass$ = DPW$ AND PWCode% = 1 THEN      'no system password
       PWCode% = -1
       GOTO Exit.Password
    END IF
	  
    SELECT CASE PWCode%
       CASE 1
	  PromptBox
	  GOSUB AskPassword
	  IF Scrt$ <> SysPass$ THEN
	     PWCode% = 0
	     GOTO Exit.Password
	  END IF
	  PWCode% = -1
	  GOTO Exit.Password
       CASE ELSE
	  GOTO Exit.Password
    END SELECT

PutSysPw:
    OPEN "MENU.QMU" FOR BINARY AS #1             'put password same as above
       LN% = LOF(1)                              'get end of file
       PUT #1, LN% - 7, SysPass$                 'back up and fill in
    CLOSE #1
    GOTO Exit.Password
   

Encoding:                                  'Encodes the PW
    Scrt$ = "Copyrite"
    Encrypt Scrt$, Temp.Pswd$
    Temp.Pswd$ = Scrt$
    RETURN

CheckState:                                 'Checks overall system pw
    IF SysPass$ = DPW$ THEN
       PWCode = -1
       GOTO Exit.Password
    END IF
    RETURN

Exit.Password:
    ScrnRest0 1, 1, 25, 80, SEG SCArray%(2000)

END SUB

DEFSNG A-Z
SUB PromptBox
    PaintBox0 23, 4, 24, 79, Shade%' Colr%(4)    'inst box shadow
    FillScrn0 22, 3, 23, 78, Colr%(4), 32
END SUB

SUB QGetKey (A$, X%)
    CheckTime& = Time2Num&(TIME$)
    A$ = ""
    WHILE A$ = ""
       A$ = INKEY$
       IF BlankTime% > 0 THEN BlankScreen CheckTime&
       IF X% THEN Timedate
    WEND

END SUB

DEFINT A-Z
SUB Screen.Char (X$) STATIC
DIM RepChar$(9), DidAsk%(9)

'This code includes the new replaceable parameters
    ExitCode = 0
    TempCom$ = ""
    Z% = INSTR(X$, "%")
    A% = INSTR(X$, "ê")                        'No return on QM.BAT
    IF A% THEN ExitCode = 4: EXIT SUB
    A% = INSTR(X$, "ë")                        'Beep for attention
    IF A% THEN
       CALL Chime(Tune%)
       X$ = LEFT$(X$, A% - 1) + RIGHT$(X$, A% - 1)
    END IF                                    'GOTO End.Msg

    A% = INSTR(X$, "µ")                        '
    B% = INSTR(X$, "Æ")
    IF A% = 0 AND B% = 0 THEN GOTO Nothing.Found
   
       IF A% = 0 AND B% > 0 THEN         'they skipped the first symbol
	  X$ = "µ" + X$                  'put it at the beginning of string
	  B% = B% + 1                    'adjust B% instr value
	  A% = 1                         'set A% to start of string
       END IF
   
       IF B% = 0 THEN                    'they forgot the closing symbol
	  X$ = X$ + "Æ"                  'put it in
	  B% = LEN(X$)                   'adjust B%
       END IF

    IF A > 1 THEN TempCom$ = LEFT$(X$, A - 1) 'get stuff before first symbol
    IF B% < LEN(X$) THEN TempEnd$ = RIGHT$(X$, LEN(X$) - (B%)) 'get ending stuff

Start.Msg:
    LgnMsg = B - A - 1
    Tempx$ = (MID$(X$, A + 1, LgnMsg))
	IF LgnMsg < 50 THEN LgnMsg = 50
    ULR = Top% + Choice%
    ULC = 39 - (LgnMsg / 2)
    LRR = ULR + 2
    LRC = ULC + LgnMsg + 3

Prnt.msg:
    ScrnSave0 ULR - 1, ULC - 1, LRR + 1, LRC + 1, SEG SCArray%(2000)

    IF MonType11% THEN
	PaintBox0 ULR - 1, ULC - 1, LRR + 1, LRC + 1, Shade%
    ELSE
	PaintBox0 ULR + 1, ULC + 1, LRR + 1, LRC + 1, Shade%
    END IF
    'Z% = 0
    FillScrn0 ULR, ULC, LRR, LRC, Colr(2), 32

    LOCATE ULR, ULC + 2
    Qprint0 Tempx$, -1
    C% = INSTR(X$, "û")
    IF C% GOTO User.Inp
    Flag% = -1
    IF INSTR(TempEnd$, "%") THEN GOTO RepChars

    IF RIGHT$(X$, 1) = "Æ" GOTO Waitinp
    Tick.Toc VAL(RIGHT$(X$, 1))         'Just get a number from 1-9
    GOTO End.Msg

Waitinp:
    LOCATE ULR + 2, ULC + 2
    Qprint0 CHR$(17) + "Press Any Key to Continue" + CHR$(16), -1
    QGetKey A$, -1

End.Msg:
    Exit.Code = 0
    ScrnRest0 ULR - 1, ULC - 1, LRR + 1, LRC + 1, SEG SCArray%(2000)
    EXIT SUB

User.Inp:
    LOCATE ULR + 1, ULC + 2
    Max = 50
    Caps.On = 0
    TextIn 0, User.Inp$, Colr%(4)        'get users input
    IF ExitCode = 2 THEN EXIT SUB        'user hit escape

    IF LEN(X$) > (C%) THEN        'check for more info on line
       X$ = User.Inp$ + RIGHT$(X$, LEN(X$) - (C%))  'strip out extra stuff
    ELSE
       X$ = User.Inp$                    'just use input
    END IF

    ExitCode = 1

    GOTO Get.Out

RepChars:
    Z% = INSTR(X$, "%")                  '
    IF Z% > 1 THEN Flag% = 0             'tell program to go for data

    WHILE Z% > 0

    Rep% = VAL(MID$(X$, Z% + 1, 1))         'MID$(X$, A + 1, LgnMsg)
    IF Rep% < 1 OR Rep% > 9 THEN GOTO NoChar
    IF RepChar$(Rep%) = "" AND NOT DidAsk%(Rep%) THEN  'If we haven't made the variable
	LOCATE ULR + 1, ULC + 2             'then lets make it
	Max = 50
	Caps.On = 0
	TextIn 0, RepChar$(Rep%), Colr%(4)  'get users input
	     IF ExitCode = 2 THEN              'user hit escape
		FOR X% = 0 TO 9                'erase flags
		    RepChar$(X%) = ""          'and everything
		    DidAsk%(X%) = 0
		NEXT X%
		EXIT SUB
	     END IF
	IF ExitCode = 2 THEN EXIT SUB       'user hit escape
	DidAsk%(Rep%) = -1
	ExitCode% = 0
	ScrnRest0 ULR - 1, ULC - 1, LRR + 1, LRC + 1, SCArray%(2000)
	EXIT SUB
    END IF

    IF Z% > 1 THEN
       IF Flag% THEN                  'This is the first % on line
	  X$ = RepChar$(Rep%) + RIGHT$(X$, LEN(X$) - (Z% + 1))
	  Flag% = 0
       ELSE                           'oops not first
	  X$ = LEFT$(X$, Z% - 1) + RepChar$(Rep%) + RIGHT$(X$, LEN(X$) - (Z% + 1))
       END IF
    ELSE
       IF LEN(X$) < (Z% + 1) THEN     'this was only % on line
	  X$ = RepChar$(Rep%)
       ELSE                           'this was not first but % was first char
	  X$ = RepChar$(Rep%) + RIGHT$(X$, LEN(X$) - (Z% + 1))
       END IF
    END IF
    Z% = INSTR(X$, "%")               'get next one
WEND

NoChar:
    ExitCode = 1

Get.Out:
    ScrnRest0 ULR - 1, ULC - 1, LRR + 1, LRC + 1, SCArray%(2000)

Nothing.Found:
    IF Z% THEN GOTO RepChars
    IF TempCom$ <> "" THEN X$ = TempCom$ + X$
    IF RIGHT$(X$, 1) = ";" THEN                 'Check for long line
       ExitCode = 3
    ELSE
       ExitCode = 1
    END IF

    IF RIGHT$(X$, 2) = ";;" THEN                'user wants ; on line
       X$ = LEFT$(X$, LEN(X$) - 1)              '  don't wrap lines around
       ExitCode = 1
    END IF




END SUB

DEFSNG A-Z
SUB Shell.Dos

    PWCode% = 1
    Password PWCode%, 4
    IF NOT PWCode% THEN EXIT SUB
    COLOR 7, 0
    CLS
   
    IF INSTR(COMMAND$, "S") THEN             'Makes batch file for new prompt
   
	PRINT "Please do not load or unload Ram resident"
	PRINT "programs while in QuickMenu Shell"
	PRINT "Type Exit to return"
       
    ELSE
	OPEN "$$HELL.bat" FOR OUTPUT AS #98
	      
		PRINT #98, "echo off"
		PRINT #98, "Prompt QuickMenu Shell $_$p$g>nul"
		PRINT #98, "cls"
		PRINT #98, "ECHO Please do not load or unload RAM resident Programs while in QuickMenu Shell"
		PRINT #98, "ECHO Type Exit to Return"
	       
	CLOSE #98
	Stuffbuf "$$HELL" + CHR$(13)
    END IF

    SHELL                      'shell out to DOS

    SetDrive (Drive$)          'reset our home drive
    CHDIR QMDir$               'change to our home directory
    IF Exist%("$$HELL.BAT") THEN KILL "$$HELL.BAT"  'kill our batch file

END SUB

DEFINT A-Z
SUB SpltColr (Colr, FG, BG)
FG = Colr MOD 16
BG = Colr \ 16

END SUB

		'Text input routine
SUB TextIn (F%, T$, EditColr%)

    SpltColr EditColr, FG, BG
    IF MonType1% THEN                    'determine monitor type
       Clr = 0                           'color
    ELSE
       Clr = 1                           'mono
    END IF

    X$ = T$                             'X$ is a working copy of input string
    ExitCode = 0: QMInsert = 0: Curpo = 1 'initialize flags

    Length = LEN(X$)
    IF Length > Max THEN EXIT SUB       'already to big to edit

    X$ = X$ + SPACE$(Max - Length)
    COLOR FG, BG
    PRINT X$;

    IF Max > 1 THEN
       PRINT "®";
       Exitpos = POS(0) - 1
       LOCATE , POS(0) - (Max + 1), 1
    ELSE
       LOCATE , POS(0) - Max, 1         'put the cursor at the beginning
    END IF
	
    GOSUB T2Insert.Off                  'set cursor size according to display
   
T2Get.Key:
    IF Curpo > Length AND QMInsert <> 0 THEN GOSUB T2Insert.Off                 'disallow insert if cursor past end
    IF Curpo > Max GOTO T2Enter         'field is filled, handle as Enter key

    A$ = INKEY$
    IF A$ = "" GOTO T2Get.Key
    IF LEN(A$) = 1 GOTO T2Regular.Key

    A$ = RIGHT$(A$, 1)                  'it was an extended key, get the code

    ON INSTR("GKMORSHP", A$) GOTO T2Home, T2Left, T2Right, T2EndKey, T2Ins, T2Del, TUp, T2Enter
   
    IF F% THEN GOTO T2Get.Key               'filter out function keys

    GOTO T2Get.Key                      'none of the above, get again
   
T2Home:
    LOCATE , POS(0) - (Curpo - 1)       'put cursor at beginning of line
    Curpo = 1                           'show cursor as being on 1st character
    GOTO T2Get.Key
					
T2Left:
    IF Curpo = 1 GOTO T2Get.Key         'cursor is on the first character, so ignore it
    Curpo = Curpo - 1                          'update Curpo
    PRINT CHR$(29);                     'print a backspace
    GOTO T2Get.Key


T2Right:
    Curpo = Curpo + 1                   'update Curpo
    PRINT CHR$(28);                     'advance the cursor on the screen
    GOTO T2Get.Key


T2EndKey:
    LOCATE , POS(0) + (Length - Curpo) + 1 'put cursor at the end of the line
    Curpo = Length + 1                     'update Curpo
    GOTO T2Get.Key

T2Ins:
    IF QMInsert THEN
       GOSUB T2Insert.Off
       GOTO T2Get.Key                   'insert is already on, turn it off
    END IF

    IF Curpo > Length GOTO T2Get.Key    'ignore Ins if cursor is past the end
    IF Length = Max GOTO T2Get.Key      'also ignore if field is full
    QMInsert = 1                        'set the insert flag
				       
    IF Clr THEN                         'set cursor size according to display
       LOCATE , , , 0, 7
    ELSE
       LOCATE , , , 0, 13
    END IF

    GOTO T2Get.Key

T2Del:
    IF Curpo > Length GOTO T2Get.Key    'ignore Del key if cursor is past end

    FOR A = Curpo TO Length - 1
	A$ = MID$(X$, A + 1, 1)
	MID$(X$, A, 1) = A$             'move all characters one position back
	PRINT A$;                       'reprint the moved characters
    NEXT

    MID$(X$, Length, 1) = " "           'erase the last character
    PRINT " ";

    LOCATE , POS(0) - (Length - Curpo + 1)
    Length = Length - 1                        'show string as one character shorter
    GOTO T2Get.Key

TUp:
    ExitCode = 1
    GOTO T2Enter                        'handle as if it were the Enter key
   
T2Regular.Key:

    IF A$ < " " THEN                    'a control key
       ON INSTR(CHR$(8) + CHR$(13) + CHR$(27), A$) GOTO T2Backspace, T2Enter, T2Escape
       GOTO T2Get.Key                   'none of the above
    END IF
   
    IF Caps.On THEN A$ = UCASE$(A$)     'capitalize if requested
   
    IF F% THEN                          'filter for filenames
       A$ = UCASE$(A$)
       SELECT CASE A$
	 CASE "A" TO "Z", "0" TO "9", ".", "\", ":", "_"
      
	 CASE ELSE                      'Skip any punctuation etc...
	    CALL Chime(Tune%)
	    GOTO T2Get.Key
	END SELECT
   
    END IF

    IF Num.Only THEN                    'disallow non-numeric if requested
       IF A$ < "0" OR A$ > "9" THEN
	  CALL Chime(Tune%)
	  GOTO T2Get.Key
       END IF
    END IF
					    
    PRINT A$;                           'print character
    Curpo = Curpo + 1                   'show cursor being ahead

    IF QMInsert GOTO T2Handle.Insert
    MID$(X$, Curpo - 1, 1) = A$         'assign the character
    IF Curpo > Length + 1 THEN Length = Curpo - 1   'cursor is past end, increase length
    IF Length = Max AND Curpo > Length GOTO T2Enter 'field complete, handle as Enter key
    GOTO T2Get.Key
   

T2Handle.Insert:
    Length = Length + 1                 'show string being 1 character longer

    FOR A = Length TO Curpo STEP -1     'move all characters 1 position ahead
	Temp$ = MID$(X$, A - 1, 1)
	MID$(X$, A, 1) = Temp$
    NEXT

    MID$(X$, Curpo - 1, 1) = A$         'assign the current character
    PRINT MID$(X$, Curpo, Length - Curpo + 1);  're-print characters in new position
    LOCATE , POS(0) - (Length - Curpo + 1)      'position the cursor

    IF Length = Max GOTO T2Enter        'field complete, handle as Enter key
    GOTO T2Get.Key


T2Backspace:
    IF Curpo = 1 GOTO T2Get.Key         'can't back up any more, ignore
    Curpo = Curpo - 1                          'show cursor being 1 character before
    PRINT CHR$(29);                     'back up the cursor
    GOTO T2Del                          'handle as if it were the Delete key
   
T2Enter:
    GOSUB T2Insert.Off                  'clear insert, restore cursor size
    X$ = LEFT$(X$, Length)              'retain only the current length

    T$ = X$                             'assign the string
    IF Exitpos > 0 THEN LOCATE , Exitpos: PRINT " ";       'Clear End Mark
    LOCATE , , 0                        'turn off the cursor
    EXIT SUB
   
T2Escape:
    ExitCode = 2                        'show that the user pressed Escape
    GOTO T2Enter                        'handle as if it were the Enter Key

T2InsertLine:                            'F8
    ExitCode = 9
    GOTO T2Enter
   
T2deleteLine:                            'F7
    ExitCode = 10
    GOTO T2Enter

T2Insert.Off:                           'clear Insert mode and restore cursor,
					'  depending on monitor type
    QMInsert = 0

    IF Clr THEN
       LOCATE , , , 6, 7
    ELSE
       LOCATE , , , 12, 13
    END IF

    RETURN

END SUB

SUB Tick.Toc (X)
	  
    X! = TIMER
    WHILE TIMER < X! + X: WEND

END SUB

SUB Timedate STATIC
    LOCATE 25, 71, 0
    IF NumLock% THEN Qprint0 "NUM", -1 ELSE Qprint0 TxFil$, -1
    LOCATE , 75, 0
    IF CapsLock% THEN Qprint0 "CAP", -1 ELSE Qprint0 TxFil$, -1

    IF LastTime$ = TIME$ THEN EXIT SUB  'Print time only if it changes
    LOCATE 3, 4, 0
    Qprint0 TIME$, -1
    LOCATE , 68, 0
    Qprint0 DATE$, -1
    LastTime$ = TIME$                   'Update LastTime$

END SUB

SUB Trail1                              'Get Current File Name

DIM Trail$(50), Choice$(50)
   
    IF NOT Exist%("TRAIL") THEN CheckBye 'Leave if not here
    C = 0                               'Set counter to 0

    OPEN "Trail" FOR INPUT AS #1
       LINE INPUT #1, Menufile$         'Get Name of MenuProg
       LINE INPUT #1, LastDate$         'Get Last Date written to
	 
       WHILE NOT EOF(1)                 'Get Trail files
	  C = C + 1
	  IF C > 50 THEN C = 1          'Backtrack files up to 50
	  LINE INPUT #1, Trail$(C)      'Get file Name
	  LINE INPUT #1, Choice$(C)     'Get Last Choice Number
       WEND
    CLOSE #1

    IF C = 0 THEN                       'If no place to backup
       KILL "Trail"                     'then kill the dude
       Current.Menu$ = "MENU"           'Set current to default
       CheckBye                         'Are we leaving ?
    END IF

    IF Trail$(C) = "" THEN              'Default to Menu
       Current.Menu$ = "Menu"
       EXIT SUB
    END IF

    Current.Menu$ = Trail$(C)           'Set Current.Menu to Top Choice
    Choice = VAL(Choice$(C))            'Set Last Choice to Top Choice
    IF C = 1 THEN EXIT SUB              'If only 1 last name-return
    OPEN "Trail" FOR OUTPUT AS #1       'Decrement Menu name stack
       PRINT #1, Thisfile$              'Record This file Name
       PRINT #1, DATE$                  'Date Stamp last usage
       FOR X = 1 TO C - 1               'Record trail, less current menu
	   PRINT #1, Trail$(X)
	   PRINT #1, Choice$(X)
       NEXT X
    CLOSE #1

END SUB

SUB Trail2
			   'Add name to stack
    IF NOT Exist%("TRAIL") THEN
       Build.Trail
       EXIT SUB
    END IF

    OPEN "Trail" FOR APPEND AS #1
       PRINT #1, Current.Menu$
       PRINT #1, STR$(Choice)
    CLOSE #1

END SUB

DEFSNG A-Z
FUNCTION YN% (X%)
   
    QGetKey A$, X%
    Y% = INSTR("Y", UCASE$(A$))
    YN% = Y% * -1

END FUNCTION

