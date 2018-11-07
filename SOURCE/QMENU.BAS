'********** QuickMENU 3.2 - by Jay Munro
'Copyright (c) 1989 Jay Munro
'Copyright (c) 1989 Crescent Software
'revision 8/90  Version 3.2
'QuickBASIC 4.5 version - load into the QB 4.5 editor with Pro.QLB
'For distribution rights please call Crescent Software

'Assembly Routines from QuickPak Professional
'Note - Release version compiled with BC7.1
'EXE file compiled with BC7.1      Approx size 75K
'BC QMENU /O/S/FPA;
'LINK /EX /NOE QMENU.OBJ + NOLPT.OBJ + NOCOM.OBJ + NOGRAPH.OBJ + NOEVENT.OBJ + SMALLERR.OBJ,,NUL,PRO.LIB;
'NOCOM.OBJ, NOLPT.OBJ, NOGRAPH.OBJ & SMALLERR.OBJ are
'contained in the BC 7.1 compiler libraries.
'
'To compile & link with QB4.5
'BC QMENU /O;
'LINK /EX /NOE QMENU.OBJ + NOCOM.OBJ,,NUL,PRO.LIB;
'
'========================= Files used by Quick Menu =========================
'
' Trail - keeps track of last menu/choice selection up to 50 levels
' QM.Bat - created batch file that runs program choices
' *.QMU - menu files for each menu
' QMenu.QSL - title and help screens in QBase library format

' Command line switches    D - disables 1/1/80 date checking
'                          N - disables sound on errors or messages
'                          S - used internally only for DOS shell message

'============================= Declaration Dept =============================

'Declarations made to simplify calling syntax, since the subroutines may
'be called like BASIC keywords.  For example, "Inc A" calls the subroutine
'"Inc" to increment the value of A.  If a subprogram is not declared it
'would be called "CALL Inc (A)".  This is better, right?

DEFINT A-Z
DECLARE SUB AsciiBox (Texture%)              'Full ascii chart for background characters
DECLARE SUB Aprint0 (BYVAL A, B, C, D, E)    'Prints an array on screen
DECLARE SUB BarMenu (Item$(), Choice)        'Main Menu Engine
DECLARE SUB BlankScreen (X&)                 'Blanks screen after preset time
DECLARE SUB Build.Trail ()                   'Logs last menu & selection
DECLARE SUB BuildQmBatch ()                  'Builds QM.Bat file to run progs
DECLARE SUB CheckBye ()                      'Makes sure user wants to leave
DECLARE SUB CheckColor (Colr)                'Checks for illegal color combinations
DECLARE SUB ColorChoice (Clr, CL$)           'Color selection sub
DECLARE FUNCTION CapsLock% ()                'Check CapsLock key
DECLARE FUNCTION NumLock% ()                 'Check NumLock Key
DECLARE SUB SpltColr (Colr, FG, BG)          'Parses FG,BG from Colr
DECLARE SUB Default.Colr (X)                 'Sets Default colors for screen
DECLARE SUB DefineColors (CL$())             'User selectable color sub
DECLARE FUNCTION DosError%                   'Returns last DOS error
DECLARE SUB Encrypt (s$, PW$)                'Encodes password
DECLARE FUNCTION Exist% (X$)                 'Checks for existance of file
DECLARE SUB FileImport (Count%, X%)          'Import text into Full Screen editor
DECLARE SUB FSEdit ()                        'Full Screen Editor for commands
DECLARE SUB Home.Base ()                     'Checks for existance of QMenu.EXE
DECLARE FUNCTION Homemenu% ()                'Checks if home menu
DECLARE FUNCTION GetDir$ (Drive$)            'Gets current default directory
DECLARE FUNCTION GetDrive% ()                'Gets current default drive
DECLARE SUB GetScrn (ScrName$, Lib(), Flag)  'Gets Screen by name
DECLARE SUB Help ()                          'Loads and shows help screens
DECLARE SUB Inst.Box ()                      'Prints commands available
DECLARE SUB LibNo (ScrName$, Lib(), N, Flag) 'Converts Screen Name to Number
DECLARE SUB LoadLib (Libname$, Flag)         'Loads Logo & Help
DECLARE SUB LoadLogo (X)                     'Loads Logo Screen if present
DECLARE SUB Log.It (CNT)                     'Logs latest changes in menu
DECLARE FUNCTION MonType1% ()                'Gets current monitor type
DECLARE SUB Password (X%, Y%)                'What else
DECLARE SUB QGetKey (A$, X%)                 'Waits and returns key
DECLARE SUB Promptline (A$)                  'Displays Selection Promptline
DECLARE SUB PromptBox ()                     'Displays prompt box at bottom of screen
DECLARE SUB QBload (Libname$, SEG ScrnArray) 'Bload that works with DOS 2.1
DECLARE SUB Qprint0 (X$, X)                  'Prints with color specified
DECLARE FUNCTION ReadTest% (File$)           'Check if drive is readable
DECLARE SUB ScrnSave0 (UR, UC, LR, LC, SEG Ary)       'Saves Screen
DECLARE SUB ScrnRest0 (UR, UC, LR, LC, SEG Ary)       'Restores screen
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
DECLARE SUB FillScrn0 (UR%, UC%, LR%, LC%, Cr%, Char%)   'Makes color window
DECLARE FUNCTION WriteTest% (File$)          '
DECLARE SUB DiskTest (File$, X%, Mode%)      'Checks if disk is ready
DECLARE FUNCTION YN% (X%)                    'Yes no function
DECLARE SUB PaintBox0 (UR%, UC%, LR%, LC%, Colr) 'Paints area without changing it
DECLARE SUB Zero.Out (X$)                    'Replaces space chars with _

DATA Copyright (c) 1989 Jay Munro
DATA Copyright (c) 1989 Crescent Software


'============================================================================
'                  Setup variables and check environment
'============================================================================
DIM SHARED FG, BG, Colr, Max, ExitCode, Num.Only, Caps.On, LastDate$, BlankTime%
DIM SHARED No.Choice, Max.Len, Num$(12), Item$(12, 22), Pswd$(10)
DIM SHARED Choice, Temp.Pswd$, Current.Menu$, ScrnArray(X), Top%
DIM SHARED LibFlag, Drive$, QMDir$, Thisfile$, PWCode%, SysPass$, Tune%
DIM SHARED Colr(9), Colr$(8), CL$(9), PreHelp, Shade%, Texture%, TxFil$

CONST DPW$ = "Crescent"

CT = 1                                  'Initialize count

Size% = 22
DIM SHARED Text$(Size%)                 'temporary edit/add variable for item$
Size% = 6800
DIM SHARED SCArray%(Size%)

LibFlag = -1                            'Preset LibFlag true for no help

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

IF Drive$ = "" OR QMDir$ = "" THEN      'disk errors , bag out
   LOCATE 1, 1
   PRINT "Disk Error - please correct and restart QuickMenu"
   END
END IF

'============================================================================
'  Get Preliminary information
'============================================================================
'Automatic Date checking
  
IF INSTR(COMMAND$, "D") THEN                      'Skip the time and date prompt
	Thisfile$ = "QMENU " + COMMAND$           'Preserve command line in batch file
ELSE
	Thisfile$ = "QMENU " + COMMAND$           'Get the time and date prompt
	IF DATE$ = "01-01-1980" THEN
		 CLS
		 PRINT "Please set the date & Time or press enter to skip"
		 SHELL "Date"
		 SHELL "Time"
	END IF
END IF
IF INSTR(COMMAND$, "N") THEN Tune% = 99


'Check date against last time used
IF Exist%("Trail") THEN                  'If trail exists, read date
   OPEN "Trail" FOR INPUT AS #1          '  trash menu name
	 LINE INPUT #1, X$
	 LINE INPUT #1, LastDate$
   CLOSE #1

   IF LastDate$ = DATE$ THEN             'was the lasttime used today ?
	Trail1                           'yes, pop menu name last used
   ELSE
	CALL KillFile("Trail")           'no, kill it
	LastDate$ = DATE$                'set last date used to today
	Build.Trail                      'make a new trail
	LoadLogo 1                       'show the logo
   END IF
ELSE
	LastDate$ = DATE$                    'if no trail existed
	Build.Trail                          'build trail to start
	LoadLogo 1                           'show the logo
END IF

'===========================================================================
Begin:
	ERASE Item$                         'Clear Item$ to start
	ERASE Pswd$                         'Clear password also
	IF NOT Exist%(Current.Menu$ + ".QMU") THEN
	   GOTO Build.Menu                  'Build it
	END IF
	Password 0, 4

Start:
	ExitCode = 0                        'Start from scratch
	GOSUB Get.Menu                      'Load Item$() with menu choices
	TxFil$ = STRING$(3, Texture%)
	GOSUB Screen.One                    'Show the screen
'==========================================================================
'                     Sub - Routines start here
'===========================================================================
Menu.Display:                           '** Puts Menu On Screen **
	Inst.Box                            'Show the instructions
	PreHelp = 0                         'Set help screen to the first one
	No.Choice = -1                      'Tell BarMenu to take choices
	Max.Len = 30                        'Menu can only be 30 chars wide
	ExitCode = 0                        'Reset ExitCode
	IF Choice = 0 THEN Choice = 1       'Eliminate 0 menu item
	IF Item$(1, 0) = "" GOTO Build.Menu 'Blank menu (usually a mistake)
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
	   CASE 6                           'F10 key
	  X% = 1
	  Password X%, 4
	  IF NOT X% THEN GOTO Menu.Display
	  GOTO Edit.Choice
	   CASE 8                           'Alt-F5 - fast exit
	  BuildQmBatch
	   CASE 9                           'Alt M restarts to main menu
	  IF Exist%("Trail") THEN       'check for the trail file
		CALL KillFile("Trail")  'kill it so we don't return
		Choice% = 1             'reset our choice
		Build.Trail             'make a clean trail file
		Trail1                  'log it
		GOTO Start              'restart
	   ELSE
		GOTO Menu.Display
	   END IF
	  
	   CASE ELSE
	END SELECT

	Password X%, 1                      'Normal password prompting
	IF NOT X% THEN
	   CALL Chime(Tune%)                        'Sound routine from Pro II
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
   
	FillScrn0 1, 1, 25, 80, Colr(2), Texture%  'Clear Screen
   
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

'=================== Editing selections =====================================
Edit.Choice:                            'F10 gets you here - get choices
	PromptBox
	Promptline "Your Choice Please"     'Display prompt
		
	LOCATE 22, 5                        'help items
	  Qprint0 "<A>dd Item    <C>olors    <E>dit Item    <D>elete Items    <T>itle Change", -1
	LOCATE 23, 7
	  Qprint0 "<S>ystem Password    <B>ackground Character    <P>hospher Protection", -1


Get.Choice:
	LOCATE 24, 39, 0                          'Locate & turn off cursor
	QGetKey Text$, -1                         'get selection - enable time/date

	SELECT CASE Text$
	   CASE CHR$(27), CHR$(13)                'Enter or Esc pressed
	  GOTO Menu.Display                   'start again
	   CASE CHR$(0) + ";"                     'F1 help pressed
	  PreHelp = 2                         'skip intro screen
	  Help
	  GOTO Start
	   CASE ELSE
	END SELECT

	SELECT CASE UCASE$(Text$)
	   CASE "A"                               'Add
	  GOTO Add.Choices
	   CASE "E"                               'Edit
	  GOTO Single.Edit
	  GOTO Menu.Display
	   CASE "D"                               'Delete
	  GOTO Delete.Query
	   CASE "C"                               'Colors
	  DefineColors CL$()
	  GOTO Start
	   CASE "T"                               'Title edit
	  GOTO Title.Edit
	   CASE "L"                               'Look at logo
	  LoadLogo 1
	   CASE "B"                               'Change Background
	  AsciiBox Texture%                   '  texture char
	  IF ExitCode <> 2 THEN Log.It VAL(Item$(0, 1))
	   CASE "S"                               'Change System Password
	  Password 2, 4
	  GOTO Start
	   CASE "P"                               'Screen Blanking Prompting
	  PromptBox
	  LOCATE 23, 20
		Qprint0 "Set to 0 for no screen blanking", -1
	  LOCATE 22, 15
		Qprint0 "Enter number of minutes of inactivity to blank screen", -1
	  LOCATE 23, 55
	  Max = 2                             'Allow only up to 99 minutes
	  Num.Only = 1
	  Temp$ = LTRIM$(STR$(BlankTime% / 60))  'Blanktime% is in seconds
	  TextIn 0, Temp$, Colr%(4)              ' so divide by 60 for display
	  Num.Only = 0
	  IF ExitCode = 2 THEN GOTO Menu.Display 'ESC forgets changes
	  IF VAL(Temp$) * 60 <> BlankTime% THEN
		 BlankTime% = VAL(Temp$) * 60        'Make back into seconds for
		 Log.It VAL(Item$(0, 1))             ' system and save it
	  END IF
	   CASE ELSE
	  GOTO Get.Choice
	END SELECT

GOTO Start

'==============================================================================
Single.Edit:                            'Edit a selection
	PreHelp = 3
	PromptBox
	Promptline "Select Item to Edit"
	BarMenu Num$(), Choice              'Get one
	IF ExitCode = 2 GOTO Menu.Display   'Escape pressed
	CT = Choice                         'Set Choice
	Password X%, 1                      'Check if password on item
	IF NOT X% THEN                      'Sorry wrong password
	   CALL Chime(Tune%)                        'Sound routine from Pro II
	   GOTO Menu.Display
	END IF
	Promptline "<Enter> For no change    <ESC> to Cancel"
NameHere:                               'Edit Name of selection
	LOCATE 22, 20
	Qprint0 "Item Name: ", Colr%(4)
	GOSUB Text.Item                     'Load Temp Array
	Caps.On = 0
	Max = 30
	LOCATE 22, 31
	TextIn 0, Text$(0), Colr%(4)        'Edit Item name
	IF Text$(0) = "" THEN GOTO Menu.Display

	SELECT CASE ExitCode
	   CASE 1
	  GOTO Single.Edit
	   CASE 2
	  GOTO Menu.Display
	   CASE ELSE
	END SELECT
	  
	Edit.Flag = -1

MHand2:
	Password Pswd%, 3
   
	GOSUB MenuHandler                   'Is it a Menu or Dos Item
	SELECT CASE ExitCode
	   CASE 0                           'Dos Item
	  GOTO Command.Edit
	   CASE 1                           'Up arrow
	  GOTO NameHere
	   CASE 2                           'Escape
	  GOTO Menu.Display
	   CASE 3                           'Menu item
	FOR X = 2 TO 20                 'Clear array elements
	   Text$(X) = ""                ' to eliminate later problems
	NEXT X
	GOTO Leave
	END SELECT

Command.Edit:
	FSEdit                              'Goto fullscreen editor for commands
	SELECT CASE ExitCode
	   CASE 1                           'Up arrow
	  GOTO MHand2
	   CASE 2                           'Esc key
	  GOTO Menu.Display
	   CASE ELSE
	END SELECT

Leave:
	Temp.CT = Choice
	Insert.flag = 1
	GOSUB Item.Text
	Log.It VAL(Item$(0, 1))
	GOTO Menu.Display

'===========================================================================

Delete.Query:                           'Delete Item
	PreHelp = 7
   
	PromptBox
	Promptline "Select Item to Delete"
	  
	BarMenu Num$(), Choice
	IF ExitCode = 2 GOTO Menu.Display   'Edit.Choice
	Password X%, 1
	IF NOT X% THEN
	   CALL Chime(Tune%)                        'Sound routine from Pro II
	   GOTO Menu.Display
	END IF

	LOCATE 22, 32 - (LEN(Item$(Choice, 0)) / 2)
	Qprint0 "Delete Item =>  " + Item$(Choice, 0), -1

	LOCATE 23, 30
	Qprint0 "Are You Sure ? (Y/N)", Colr(6)     'Prompt
	IF NOT YN%(-1) GOTO Menu.Display            'If no then bag out

Delete.It:
	FOR CT = Choice TO VAL(Item$(0, 1)) - 1     'CT = 1 less total
	FOR X = 0 TO 22                         'loop through commands
		Item$(CT, X) = Item$(CT + 1, X)     'Copy commands down one item
	NEXT X                                  '  to fill in hole made
	Pswd$(CT) = Pswd$(CT + 1)               'Get the password
	NEXT CT                                     'Get next item

	IF Choice = VAL(Item$(0, 1)) THEN Choice = Choice - 1'Adjust choice if last item
	IF Choice < 1 THEN Choice = 1               'Force 1 for choice
	  
	IF (VAL(Item$(0, 1)) - 1) < 1 THEN                              'Erased the last item
	   ERASE Item$                              'so clear array
	   CALL KillFile(Current.Menu$ + ".QMU")    'Erase menu file
	   GOTO Start                               'start again
	END IF

	Item$(0, 1) = STR$(VAL(Item$(0, 1)) - 1)    'Adjust total item count
	FOR X = 0 TO 22                             'Clear array element
	Item$(VAL(Item$(0, 1)) + 1, X) = ""
	NEXT X

	Log.It VAL(Item$(0, 1))                     'Save everything
	GOTO Start

'===========================================================================
MenuHandler:
	' ExitCodes used
	' 0  = Dos command
	' 1  = Up arrow
	' 2  = Escape
	' 3  = Menu commmand

TextHere:                                       'Prompt for DOS/menu items
	LOCATE 23, 20
	Qprint0 "<M>enu or <D>OS command ", Colr(4)
	Caps.On = 1
	Max = 1
	ExitCode = 0
	LOCATE 23, 44
	Temp$ = Text$(22)
	TextIn 0, Text$(22), Colr%(4)
	FillScrn0 23, 3, 23, 77, Colr%(4), 32
	IF ExitCode = 1 OR ExitCode = 2 THEN RETURN 'Up arrow or ESC
				 
	IF Text$(22) = "" THEN ExitCode = 2: RETURN 'Return key pressed, considered ESC
	Text = INSTR("MD", Text$(22))               'which is it

	SELECT CASE Text
	   CASE 0                                   'Not either, get again
	  GOTO TextHere
	   CASE 1                                   'Menu item
	  GOTO Menu.Cmd
	   CASE 2                                   'DOS item
	  ExitCode = 0
	  RETURN
	   CASE ELSE
	END SELECT

Menu.Cmd:
	LOCATE 23, 47
	Qprint0 "No Extensions Please         ", Colr(4)
	LOCATE 23, 20
	Qprint0 "Menu File Name: ", Colr(4)
	Caps.On = 1: Max = 8
	IF Edit.Flag AND Temp$ = Text$(22) THEN     'if it used to be a DOS
	   Text$(1) = LEFT$(Text$(1), 8)            ' item, clear it
	ELSE
	   Text$(1) = ""
	END IF
	  
	LOCATE 23, 37
	TextIn -1, Text$(1), Colr%(4)               'Get menu name
	IF ExitCode = 2 THEN RETURN
   
	Zero.Out Text$(1)                           'Convert any spaces to _

	IF Text$(1) = "MENU" THEN                   'sorry this is in use
	   CALL Chime(Tune%)                        'Sound routine from Pro II
	   LOCATE 23, 47
	   Qprint0 "`MENU'is a reserved name", Colr(6)  'Fair Warning
	   Tick.Toc 2
	   GOTO Menu.Cmd
	END IF
	  
	FillScrn0 23, 3, 23, 77, Colr%(4), 32
   
	IF ExitCode = 2 THEN RETURN
	IF ExitCode = 1 THEN GOTO TextHere
	IF Text$(1) = "" THEN GOTO Menu.Cmd
	  
	ExitCode = 3
	RETURN

'===========================================================================

Menu.Change:
	Last.Menu$ = Current.Menu$          'Set Menu we're leaving
	Trail2                              'Log Change on Trail
	Current.Menu$ = Item$(Choice, 1)    'Pick up new title
	Choice = 1                          'Reset Choice
	GOTO Begin                          'Go get menu

'===========================================================================

Title.Edit:                             'Edit Title Name
	PreHelp = 7                         'Set Help screen
	GOSUB Title.Enter                   'Enter title
	GOTO Menu.Display                   'Start

Title.Enter:
	Promptline "Edit Menu Title"
	PromptBox
	LOCATE 23, 20
	Qprint0 "Menu Title ", Colr(4)
   
	Caps.On = 0
	Max = 30
	IF Item$(0, 0) = "Your Title Here" THEN     'Clean slate unless
	   Temp$ = ""                               'Legit title exists
	ELSE
	   Temp$ = Item$(0, 0)
	END IF
	ExitCode = 0
	LOCATE 23, 32
	TextIn 0, Temp$, Colr%(4)
   
	IF ExitCode = 2 THEN                        'if escape handle it
	  IF Homemenu THEN
		 ExitCode = 5
		 BuildQmBatch
		 GOTO Earlyout
	  ELSE
		 Trail1
		 GOTO Start
	END IF
	END IF
	  
Earlyout:
	IF Temp$ = "" THEN GOTO Title.Enter     'Get title or else
	IF ExitCode = 2 THEN RETURN             ' unless escape
	Item$(0, 0) = Temp$                     'If valid then keep it
	Log.It VAL(Item$(0, 1))                 'Log changes
	GOSUB LogoBox
	RETURN

'===========================================================================

Add.Choices:                            'Add to Menu
	PreHelp = 2
	CNT = VAL(Item$(0, 1))              'Set CNT to # of Current menu choices
	CT = VAL(Item$(0, 1)) + 1           'Set counter = Menu Count + 1
	IF CT < 1 THEN CT = 1               'Keep counter between 1 - 9
	IF CT > 9 THEN                      'Menu Array filled
	  CALL Chime(Tune%)             'Sound routine from Pro II
	  ScrnSave0 12, 27, 16, 54, SEG SCArray%(2000)
	  PaintBox0 13, 28, 16, 54, Shade
	  FillScrn0 12, 27, 15, 53, Colr(6), 32
	  LOCATE 13, 28
	  Qprint0 "Sorry no more selections", Colr(6)
	  LOCATE 14, 32
	  Qprint0 "Try adding a menu", Colr(6)
		 Tick.Toc 2
	  ScrnRest0 12, 27, 16, 54, SEG SCArray%(2000)
	   GOTO Menu.Display                'exit
	END IF
   
	PromptBox
	Promptline "Add Items to Menu"
	GOSUB Text.Item
Add.Insert:                             'add to end or insert item
	IF First.Menu GOTO Add.Num          'If first menu, default to add
	Text$ = ""
	LOCATE 22, 25
	Qprint0 "Add selection" + STR$(CT) + " ? ", Colr(4)

	Max = 1
	Caps.On = 1
	LOCATE 22, 43
	TextIn 0, Text$, Colr%(4)
	IF ExitCode = 2 GOTO Start
	IF Text$ = "" THEN
	   First.Menu = -1
	   GOTO Add.Num
	END IF
				 
	Text = INSTR("123456789NY", Text$)  'If user selected number use it
	SELECT CASE Text
	   CASE 1 TO 9                      'selected number
	  Temp.CT = Text
	  Insert.flag = 0
	  GOTO Add.It
	 
	   CASE 10                          '"No"  prompt for number
	  GOTO Insert.Num
	 
	   CASE 11                          '"Yes" then just add
	  First.Menu = -1
	  GOTO Add.Num
	 
	   CASE ELSE
	  GOTO Add.Insert
	END SELECT

Insert.Num:                             'Insert prompt
	PromptBox
	LOCATE 22, 27
	  Qprint0 "Insert at what # ", Colr(4)
	Insert.flag = 0
	Text$ = ""
	Max = 1
	Num.Only = 1                        'Numbers only
	LOCATE 22, 45
	TextIn 0, Text$, Colr%(4)               'Get number
	Num.Only = 0                        'Set back to text
	IF ExitCode = 2 GOTO Start
	Temp.CT = VAL(Text$)                'Add Item number
	IF Temp.CT > CT GOTO Insert.Num
	GOTO Add.It

Add.Num:                                'Default number
	Insert.flag = 1                     'Add to end of list
	Temp.CT = CT

Add.It:
	PromptBox
	LOCATE 22, 20
	Qprint0 "Item" + STR$(Temp.CT) + " Name: ", Colr(4)

	Num.Only = 0
	Caps.On = 0
	Max = 30
	LOCATE 22, 34
	TextIn 0, Text$(0), Colr%(4)
	IF ExitCode = 2 GOTO ExitAdd        'Edit.choice
	IF Text$(0) = "" GOTO ExitAdd       'Edit.choice

MHand:
	Password Pswd%, 2
   
	Text$(22) = "": Text$(1) = ""
	GOSUB MenuHandler
	FillScrn0 23, 4, 23, 78, Colr%(4), 32

	SELECT CASE ExitCode
	   CASE 0
	  Text$(22) = "D"
	  X = 1
	  GOTO Add.up
	   CASE 1
	  GOTO Add.It
	   CASE 2
	  Choice = Choice - 1
	  GOTO ExitAdd
	   CASE 3
	  GOTO Add.CMD
	END SELECT
	IF Text$(22) = "" THEN GOTO ExitAdd        'user pressed down arrow
Add.up:
	
	Choice = Temp.CT                    'Set choice to goto FSEdit
	FSEdit
	
	IF ExitCode = 2 THEN
	   Choice = Choice - 1
	   GOTO ExitAdd                     'Escape, get lost
	END IF
	IF ExitCode = 1 THEN GOTO MHand     'Up arrow, back up

Add.CMD:
	GOSUB Item.Text

Add.menu:
	PromptBox
	CNT = CNT + 1
	Log.It CNT
	CT = CT + 1
	IF CT = 9 GOTO Start               'If array filled then end adding
	
	IF First.Menu THEN
	   No.Choice = 0
	   Max.Len = 30
	   ExitCode = 0
	   BarMenu Num$(), Choice
	   GOTO Add.Choices
	END IF

ExitAdd:
	First.Menu = 0
	GOTO Start

'=================== Temporary Text$ Handlers ===========================

Text.Item:                              'Load temporary variable
	FOR X = 0 TO 22
	Text$(X) = Item$(CT, X)
	NEXT X
	Temp.Pswd$ = Pswd$(CT)
	RETURN

Item.Text:                              'Unload temporary variable if not inserted
	IF Insert.flag = 1 GOTO STRT.text
	FOR Inst = VAL(Item$(0, 1)) TO Temp.CT STEP -1
	FOR X = 0 TO 22
		Item$(Inst + 1, X) = Item$(Inst, X)
	NEXT X
	Pswd$(Inst + 1) = Pswd$(Inst)
	NEXT Inst

STRT.text:                              'Unloads temp var if an insert is made
	CT = Temp.CT
	FOR X = 0 TO 22
	Item$(Temp.CT, X) = Text$(X)
	NEXT X
	Pswd$(CT) = Temp.Pswd$

	Num$(Temp.CT) = STR$(Temp.CT) + "  " + Item$(Temp.CT, 0)
	CT = VAL(Item$(0, 1))               'Sets CT to Item numbers
	RETURN

'===========================================================================

Build.Menu:
	ERASE Item$                                 'Clear Item array
	ERASE Pswd$
   
	IF Homemenu THEN Default.Colr 0             'Get default colors to start
	
	GOSUB Screen.One                            'Show Screen
	CALL Chime(Tune%)                           'Sound routine from Pro II
   
	PaintBox0 10, 28, 14, 54, Shade%
	FillScrn0 9, 27, 13, 53, Colr(3), 32
   
	LOCATE 10, 33
	Qprint0 "No Menu Exists", -1

	LOCATE 11, 29
	Qprint0 "Press any Key to Build", -1

	LOCATE 12, 32
	Qprint0 "or <ESC> to Quit", -1

Wait.here:
	PreHelp = 0
	QGetKey Text$, -1

	IF Text$ = CHR$(27) AND Homemenu THEN           'User wants to leave
	   ExitCode = 8
	   BuildQmBatch
	END IF

	IF Text$ = CHR$(27) THEN                         'Escape
	   Trail1
	   GOTO Start
	END IF
	  
	IF Text$ = CHR$(0) + ";" THEN                    'Help requested
	   Help
	   GOTO Build.Menu
	END IF


New.Menu:                               'Name New Menu
	Choice = 1                          'Preset to choice one
	First.Menu = -1                     'Sets flag to keep adding selections
	LibFlag = -1
	GOSUB Screen.One
   
	LOCATE 3, 4, 0
	Qprint0 TIME$, -1
	LOCATE , 68, 0
	Qprint0 DATE$, -1
   
	Inst.Box
	GOSUB Title.Enter
	IF ExitCode = 2 THEN Trail1: GOTO Start
	IF Homemenu THEN SysPass$ = DPW$
	GOTO Add.Choices:


'============================== Start-up menu ===============================

Get.Menu:                             'Loads Array for current menu choices
	CheckFlag% = 0
	IF NOT Exist%(Current.Menu$ + ".QMU") THEN GOTO Build.Menu
	ERASE Item$                       'Clear Item$ to start
	ERASE Pswd$                       ' and passwords
	OPEN Current.Menu$ + ".QMU" FOR INPUT AS #1
	 LINE INPUT #1, Item$(0, 0)                  'Menu Title
	 LINE INPUT #1, Item$(0, 1)                  'Number of Items
		IF Item$(0, 1) = "" THEN                 'If no items then let's
		   CLOSE #1                              '  build a menu
		   GOTO Build.Menu
		END IF

	 LINE INPUT #1, Mix$                         'Background Texture
	
	 FOR X = 1 TO 8                              'Get the colors
		 LINE INPUT #1, Colr$(X)
		 Colr(X) = VAL(Colr$(X))
		 IF Colr(X) = 0 THEN CheckFlag% = -1
		 CheckColor Colr(X)
	 NEXT X
	  
	 FOR CT = 1 TO VAL(Item$(0, 1))              'Get all the commands
		 LINE INPUT #1, Item$(CT, 22)            '  for each menu item
		 FOR X = 0 TO 20
		 LINE INPUT #1, Item$(CT, X)
		 IF Item$(CT, X) = "" THEN EXIT FOR
		 NEXT X
	 NEXT CT
   
	 Position% = SEEK(1)                         'Get current position
							 
	CLOSE #1
	
	OPEN Current.Menu$ + ".QMU" FOR BINARY AS #1     'Get passwords
	 X$ = SPACE$(1)
	 GET #1, Position, X$                        'Skip chr$(26)
	 Position% = SEEK(1)                         'Reset position
	 Pswd$(0) = SPACE$(8)                        'PreLoad password
	 GET #1, Position, Pswd$(0)                  'Get system pw
						
	FOR X = 1 TO CT
	Pswd$(X) = SPACE$(8)                   '
	GET #1, Position% + (X * 8), Pswd$(X)  'Get passwords
	Num$(X) = STR$(X) + "  " + Item$(X, 0) 'Set up name only array for barmenu
	NEXT X
	
	CLOSE #1
	
	IF INSTR(Mix$, "-") = 0 THEN            'old pw menu had date here
	   IF INSTR(Mix$, "*") THEN             'new ones have *
	  X% = INSTR(Mix$, "*")             'format is 176*60=8
	  Texture% = VAL(Mix$)              '           |   | |
	  BlankTime% = VAL(MID$(Mix$, X% + 1)) 'texture/    | |
	  X% = INSTR(Mix$, "=")                'blanktime  /  |
	  IF X% THEN                           '              |
		 Shade% = VAL(MID$(Mix$, X% + 1))  'shadow color /
	  ELSE
		 Shade% = 8
	  END IF
	   ELSE
	  Texture% = VAL(LTRIM$(Mix$))
	  BlankTime% = 300
	  Shade% = 8
	   END IF
	END IF
	Password 3, 4
	IF CheckFlag% THEN Default.Colr 0
	RETURN
   
LogoBox:
   
	IF Item$(0, 0) = "" THEN Item$(0, 0) = "Your Title Here"

	Wth = LEN(Item$(0, 0))            'figure out width based on len of title
	UR = 3
	UC = (39 - (Wth / 2))             'center it
	LR = 5
	LC = UC + Wth + 3
   
	FillScrn0 UR, 15, UR + 4, 57, Colr(2), Texture%     'Clear old title
	PaintBox0 UR + 1, UC + 1, LR + 1, LC + 1, Shade%   'Shadow title color
	FillScrn0 UR, UC, LR, LC, Colr(1), 32   'Clear area to title color

	LOCATE 4, UC + 2
	Qprint0 Item$(0, 0), -1                'Put up new title

RETURN
   
END

'=============================== End of Main Program ========================


'Data section
ColorNames:
DATA Sh<A>dow, <T>itle, <B>ackground, <M>enu, <S>elections, <D>ate/Time
DATA <W>arnings, <H>ighlight, <E>ditor


'Assembly Language Subroutines used in QuickMenu

'Aprint0    Prints Array
'QBload     Replaces BLoad which doesn't work with DOS 2.1 under QB 4.0
'Exist      Checks existance of file
'GetDir     Gets Current Directory
'GetDrive   Gets Current Drive
'NumOff     Sets Numlock Off
'Qprint0    Quick Print with stated color
'ScrnSRA    Saves & Restores portions of screen
'SetDrive   Changes current drive default
'StuffBuf   Stuffs keyboard buffer
'FillScrn0   Makes Window with stated color, and with specific character
'Time2Num   Converts time to long int for figuring

'-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-==-=-=-=-=-=-=-
'
'This program is dedicated to my wife Kathryn and young-uns Katie & Jayson
'who have put up with the late nights, long hours and temper tantrums when
'I ran into bugs.
'Thanks Jay  8/1988

SUB AsciiBox (Texture%)
	 ExitCode = 0
	 StRow% = 4               'Character Box Row & Col
	 StCol% = 25

'Save Screen
	 ScrnSave0 StRow% - 2, StCol% - 2, StRow% + 17, StCol% + 33, SEG SCArray%(0)

'Paint shadow and background
	 PaintBox0 StRow%, StCol% - 1, StRow + 17, StCol% + 33, Shade%

'Instructions
	 CALL PromptBox           'clear prompt box
	 LOCATE 23, 9
	 Qprint0 "Select Character with Arrow keys <ESC> to cancel <Enter> to select", -1

'Put in Ascii Chart
	 LOCATE StRow% - 1, StCol% - 2
	 CALL AsciiPick(Texture%, Colr(3), Colr(6) OR 128, ExitCode)
	 
ExitStageLeft:
	 ScrnRest0 StRow% - 2, StCol% - 2, StRow% + 17, StCol% + 33, SEG SCArray%(0)

END SUB

SUB BarMenu (Num$(), Choice) STATIC          'Item$() has one dimension
	ExitCode = 0                             'Choice is the value returned
	Left.Marg = 24

'----- determine how many choices to display, and where to put the menu

	Max.Num = VAL(Item$(0, 1))               'Get Number of items to display
	Top = 11 - (Max.Num \ 2)                 'Center Menu on screen

'----- draw border and display items on the screen

Border:
	PaintBox0 Top + 1, (Left.Marg - 1), (Top + Max.Num + 3), (Left.Marg + Max.Len + 6), Shade%
	FillScrn0 Top, (Left.Marg - 2), (Top + Max.Num + 2), (Left.Marg + Max.Len + 5), Colr(3), 32

'print array of Items
	LOCATE Top + 1, Left.Marg - 1
	Aprint0 VARPTR(Num$(1)), Max.Num, 1, Max.Len + 4, Colr(3)

'print help prompt
	LOCATE (Top + Max.Num + 2), Left.Marg + 1
	Qprint0 "Use " + CHR$(24) + " or " + CHR$(25) + " and <Enter> to Select", Colr(3)
  
	IF NOT No.Choice THEN EXIT SUB              'display only
						'  don't wait for selections
'----- make inverse cursor bar over Items

Get.Loop:
	Clr = Colr(7)                       'inverse the colors
	GOSUB Display                       'make inverse bar on item

BGet.Key:
	QGetKey X$, -1
   
	SELECT CASE X$
	   CASE CHR$(13)                    'Enter key
	  EXIT SUB
	   CASE CHR$(27)                    'Escape Key
	  ExitCode = 2
	  EXIT SUB
	   CASE CHR$(0) + ";"               'Help F1
	  Help
	  LOCATE , , 0
	  GOTO BGet.Key
	   CASE CHR$(0) + "="               'F3 Shell
	  ExitCode = 3
	  EXIT SUB
	   CASE CHR$(0) + "?"               'Quit F5
	  ExitCode = 5
	  EXIT SUB
	   CASE CHR$(0) + "l"               'Quick Quit Alt(f5)
	  IF SysPass$ <> DPW$ THEN
		 ExitCode = 5               'if there is a password, then prompt
	  ELSE                          '  for it
		 ExitCode = 8               'no password just get out
	  END IF
	  EXIT SUB
	   CASE CHR$(0) + "D"               'Edit F10
	  ExitCode = 6
	  EXIT SUB
	   CASE CHR$(0) + "2"               'ALT M - returns to Main menu
	  ExitCode = 9
	  EXIT SUB
	   CASE ELSE
	END SELECT

	Clr = Colr(3)
	GOSUB Display                       'restore old item
	X = VAL(X$)                         'set X to new item

	IF X > 0 AND X <= Max.Num THEN      'Numeric Key used for selection
	   Choice = VAL(X$)
	   Clr = Colr(7)
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


'----- Mark/Unmark cursor bar Item

Display:

	LOCATE Top + Choice, Left.Marg - 1          'position cursor
						'pad with blanks if needed
	Qprint0 Num$(Choice) + SPACE$(Max.Len + 6 - LEN(Num$(Choice))), Clr
	RETURN

END SUB

SUB BlankScreen (CheckTime&) STATIC
'Blanks screen after preset time of no key activity

	 IF Time2Num&(TIME$) - CheckTime& < BlankTime% THEN EXIT SUB 'not time yet
	
	   CursorRow% = CSRLIN             'Save cursor position
	   CursorCol% = POS(1)
	   CALL ScrnSave0(1, 1, 25, 80, SEG SCArray%(4800))  'Save current screen
	   FillScrn0 1, 1, 25, 80, 7, 32    'Clear to Black
	   Flag% = -1                      'Pre set Flag% for reminder
	   WHILE INKEY$ = ""
	 
	  IF Time2Num&(TIME$) <> LastTime& THEN
		 IF Flag% THEN                      'Print Reminder logo
		FillScrn0 1, 1, 25, 80, 7, 32
		LOCATE RND(TIMER) * 23 + 1, RND(TIMER) * 70 + 1  'Random locations
		Qprint0 "QuickMenu", -1         'Print logo
		Flag% = 0                       'set to 0 so we only print once
		LastTime& = Time2Num&(TIME$)    'set lasttime for loop
		 END IF
	  ELSE
		 Flag% = -1                         'If times are equal then set flag to allow
						'printing on next clock change
	  END IF
	   WEND
	   CheckTime& = Time2Num&(TIME$)            'Reset time of last key stroke
	   LOCATE CursorRow%, CursorCol%            'Reset cursor position
	   CALL ScrnRest0(1, 1, 25, 80, SEG SCArray%(4800)) 'Put the screen back

END SUB                                         'Get back to whatever

SUB Build.Trail STATIC                  'Default Trail file
							 
	IF Exist("Trail") THEN EXIT SUB     'Don't need to build one

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
   
  NoReturn = 0                        'Preset flag for no return QM.BAT
  RunFile$ = "QM" + CHR$(13)          'Stuffbuf needs CHR$(13) to work
  Trail2                              'Add current menu/choice to stack
	 
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
		  EXIT SUB                 'Goto Start
	  CASE 3                       'Print Just User Input
		  PRINT #1, LEFT$(Item$(Choice, X), (LEN(Item$(Choice, X)) - 1));  'THIS ; is important!
	  CASE 4                       'Character detected for
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
   
	ScrnSave0 1, 1, 25, 80, SEG SCArray(0)
'    PaintBox0 12, 30, 15, 51, Shade%
   
	PromptBox

	'FillScrn0 11, 29, 14, 50, Colr(6), 32
	
	LOCATE 22, 33
	Qprint0 " Exit To DOS? ", Colr(6) OR 128

	IF SysPass$ = DPW$ THEN LOCATE 23, 39: Qprint0 "Y/N", -1
	CALL Chime(Tune%)                        'Sound routine from Pro II

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

	ScrnRest0 1, 1, 25, 80, SEG SCArray(0)

END SUB

DEFSNG A-Z
SUB CheckColor (Clr%)                 'checks for legal colors and set default
					  ' colors to Black and White
	IF MonType1% = 0 AND FNFG%(Clr%) = FNBG%(Clr%) THEN Clr% = 7: EXIT SUB
	IF Clr% = 0 OR Clr% = 8 THEN Clr% = 7             'If B+W check for illegal
							  ' combinations.
END SUB

DEFINT A-Z
SUB ColorChoice (Clr%, N$)
	ScrnSave0 4, 24, 24, 58, SEG SCArray%(2000)
	CALL PaintBox0(5, 25, 22, 58, Shade%)       'make shadow

	LOCATE 23, 40 - (LEN(RTRIM$(N$)) / 2)               'show what item is being edited
	Qprint0 RTRIM$(N$), Clr%

	LOCATE 4, 24                                'call color chart
	CALL ColorPick(Clr%, Colr%(2), ExitCode%)
	GOTO Exit.Color


Exit.Color:
	 ScrnRest0 4, 24, 24, 58, SEG SCArray%(2000)'restore piece of screen
END SUB

SUB Default.Colr (Y)            'Sets beginning color according to monitor

	Mon = MonType1%             'Get monitor type
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
	   CASE ELSE                 'Color
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

SUB DefineColors (CL$()) STATIC               'User color selection
   
	PromptBox
	A$ = " Select Item To Change Color "
	Promptline A$

	IF CL$(1) <> "" THEN GOTO Listum
	RESTORE ColorNames
	FOR X = 0 TO 8                      'Get Names of Colors To List
	READ CL$(X)
	CL$(X) = CL$(X) + SPACE$(13 - LEN(CL$(X)))
	NEXT X

Listum:                                 'Creates color box for changes
	PaintBox0 11, 33, 20, 49, Shade%
	FillScrn0 10, 32, 19, 48, 120, 32    'Colr%(4)
   
	LOCATE 19, 33
	Qprint0 "<Esc> to cancel", -1       'Colr(4)
	 
	FOR X = 1 TO 8
	LOCATE 10 + X, 34
	Qprint0 CL$(X), Colr(X)
	NEXT

Select.Here:
	QGetKey A$, -1
	 
	SELECT CASE UCASE$(A$)
	   CASE CHR$(27)                    'Esc - skip changes
	  EXIT SUB

	   CASE CHR$(13)                    'Return - Keep changes
	  GOTO Fixit

	   CASE CHR$(0) + ";"               'Help
	  PreHelp = 8
	  Help
	  LOCATE , , 0
	  GOTO Select.Here
	  
	   CASE "A"
	  ColorChoice Shade%, CL$(0)      'Shadow color
	  Shade% = Shade% AND 127
	  GOTO Listum
	  
	   CASE "T"
	  ColorChoice Colr(1), CL$(1)     'Title Color
	  GOTO Listum
	 
	   CASE "B"
	  ColorChoice Colr(2), CL$(2)     'Background color
	  GOTO Listum
	 
	   CASE "M"
	  ColorChoice Colr(3), CL$(3)     'Menu Color
	  GOTO Listum
	 
	   CASE "S"
	  ColorChoice Colr(4), CL$(4)     'Selections Color
	  GOTO Listum
	 
	   CASE "D"
	  ColorChoice Colr(5), CL$(5)     'Date/Time Color
	  GOTO Listum
	 
	   CASE "W"
	  ColorChoice Colr(6), CL$(6)     'Warnings Color
	  GOTO Listum
	 
	   CASE "H"
	  ColorChoice Colr(7), CL$(7)      'Highlight Color
	  GOTO Listum
	  
	   CASE "E"
	  ColorChoice Colr(8), CL$(8)     'Editor color Color
	  GOTO Listum
	  
	   CASE CHR$(0) + CHR$(32)            'Resets defaults
	  Default.Colr 0                  '  using selected monitor
	  GOTO Fixit

	   CASE CHR$(0) + CHR$(48)            'B+W Default Reset
	  Default.Colr 1
	  GOTO Fixit

	   CASE CHR$(0) + CHR$(46)            'Color Default Reset
	  Default.Colr 2
	  GOTO Fixit

	   CASE ELSE
	  GOTO Listum
	END SELECT

Fixit:
	CNT = VAL(Item$(0, 1))                'Save Changes
	Log.It CNT

END SUB

SUB DiskTest (File$, X%, Mode%)

	X% = -1
StartTest1:
	A% = INSTR(File$, ":")                        'Check for Colon
   
	IF A% THEN                                    'Parse out drive letter
	   TestDrive$ = MID$(File$, A% - 1, 1)
	ELSE
	   TestDrive$ = Drive$
	END IF

	IF Mode% THEN
	   X% = WriteTest%(TestDrive$)
	ELSE
	   X% = ReadTest%(TestDrive$)
	END IF
						  ' and test for file
	IF X% THEN EXIT SUB
'================================================= Warn drive not ready
	ScrnSave0 11, 25, 16, 55, SEG SCArray(4400)
	CALL Chime(Tune%)                        'Sound routine from Pro II
	PaintBox0 12, 26, 16, 55, Shade%
	FillScrn0 11, 25, 15, 54, Colr(6), 32
	LOCATE 12, 32
	Qprint0 "Drive " + TestDrive$ + ": Not Ready", -1
	LOCATE 13, 27
	Qprint0 "Correct and press any key", -1
	LOCATE 14, 28
	Qprint0 "or press <ESC> to Cancel", -1
	QGetKey A$, 0
	ScrnRest0 11, 25, 16, 55, SEG SCArray(4400)
 '=================================================
	IF A$ = CHR$(27) THEN              'If escape then just quit
	   X% = 0
	   EXIT SUB
	END IF

	GOTO StartTest1
   
END SUB

SUB FileImport (Count%, Flag%)

	ScrnSave0 12, 20, 17, 61, SEG SCArray%(4000)  'Make a window
	PaintBox0 13, 21, 17, 61, Shade%              'shadow it

PromptHere:
	FillScrn0 12, 20, 16, 60, Colr(4), 32       'give it color
	File$ = ""
						   'show Options
	IF Flag% THEN
	   LOCATE 12, 26
	   Qprint0 " Text Import up to" + STR$(21 - Count%) + " Lines ", Colr(4)
	ELSE
	   LOCATE 12, 29
	   Qprint0 " Text Export to File ", Colr(4)
	END IF

Enterfile:
	
	LOCATE 16, 27
	Qprint0 " Enter File Name or <ESC> ", Colr(4)

	LOCATE 14, 22                               'Get some text
	Max = 30
	Caps.On = 1
	TextIn -1, File$, Colr%(4)
	Caps.On = 0
	IF ExitCode = 2 GOTO NoText
	
	IF NOT Flag% GOTO Writefile                 'check readability of disk
	DiskTest File$, X%, 0
	IF NOT X% THEN GOTO NoText

	X% = Exist%(File$)
	GOSUB NoGood
	IF NOT X% THEN GOTO Enterfile

GetTheFile:

	OPEN File$ FOR INPUT AS #1
	 FOR X% = Count% TO 20
		 IF EOF(1) THEN EXIT FOR
		 LINE INPUT #1, Text$(X%)
		 Text$(X%) = LEFT$(Text$(X%), 60)
	 NEXT X%
	CLOSE #1

	Count = X%

NoText:
	ScrnRest0 12, 20, 17, 61, SEG SCArray%(4000)
	EXIT SUB

Writefile:                             'Check writeability
	DiskTest File$, X%, -1
	IF NOT X% GOTO NoText
	IF Exist%(File$) THEN GOSUB AreUSure 'Does file exist, give user out if does

	OPEN File$ FOR OUTPUT AS #1
	 FOR X% = 1 TO 20
		 IF Text$(X%) = "" THEN EXIT FOR
		 PRINT #1, Text$(X%)
	 NEXT X%
	CLOSE #1
	GOTO NoText

NoGood:
	IF NOT X% THEN
	   LOCATE 16, 28
	   Qprint0 "  Not A Valid File Name  ", Colr(6)
	   CALL Chime(Tune%)                        'Sound routine from Pro II
	   Tick.Toc 1
	END IF
	RETURN

AreUSure:                              'File exists - still use name ?
	CALL Chime(Tune%)                        'Sound routine from Pro II
	LOCATE 16, 22
	Qprint0 " That File Exists - Overwrite (Y/N) ", Colr(4)

	LOCATE 14, 22                               'Get some text
   
	IF YN%(0) THEN RETURN ELSE GOTO PromptHere
	
END SUB

SUB FSEdit                            'Full Screen Editor
  
	ScrnSave0 1, 1, 25, 80, SEG SCArray%(2000)

MainEditor:
	PreHelp = 3
	PaintBox0 2, 8, 25, 76, Shade%
	FillScrn0 1, 7, 24, 75, Colr(8), 32
   
	LOCATE 1, 26
	Qprint0 CHR$(17) + " QuickMenu Command Editor " + CHR$(16), -1
	LOCATE 2, 9
	Qprint0 "Item Name: ", -1
	LOCATE , 21
	Qprint0 Text$(0), -1

	GOSUB Reprint
	Count% = 1

EditIt:
	LOCATE 24, 9
	Qprint0 " F7-Delete line  F8-Insert line  ALT+F10-Import  ALT+F9-Export ", Colr(8)
	
	ExitCode = 0
	IF Count < 1 THEN                     'Back out to MenuHandler
	   ExitCode = 1
	   GOTO OutHere
	END IF
	
	Max = 60
	Caps.On = 0

	IF Count > 20 THEN Count = 1          'Position Cursor for editing
	LOCATE 2 + Count, 11
	TextIn 0, Text$(Count), Colr%(8)

	'Hook in here for check of un matched comment brackets
	'loop back and beep

	SELECT CASE ExitCode
	   CASE 1                                      'Up arrow
	  Count% = Count% - 1
	  GOTO EditIt
	   CASE 2                                      'Escape
	  GOTO ExitEdit
	   CASE 9                                      'F7
	  GOTO Del.Items
	   CASE 10                                     'F8
	  GOTO Insert.Items
	   CASE 20                                     'Alt F10
	  X% = Count%
	  FileImport X%, -1
	  GOSUB Reprint
	   CASE 19                                     'Alt F9
	  FileImport Count%, 0
	  GOSUB Reprint
	   CASE ELSE
	  IF Text$(Count) = "" AND Count% = 1 THEN 'First Choice 0
		 ExitCode = 2
		 GOTO OutHere
	  END IF
		  
	  IF Text$(Count%) = "" GOTO ExitEdit      'Last line blank
	  Text$(Count%) = RTRIM$(Text$(Count%))
	  Count% = Count% + 1
	  IF Count% > 20 GOTO ExitEdit

	END SELECT
	
	GOTO EditIt
   
ExitEdit:
	CALL Chime(Tune%)                        'Sound routine from Pro II
	LOCATE 24, 30
	Qprint0 " Save Changes? Y/N ", Colr(6) OR 128
	QGetKey A$, 0
	  
	SELECT CASE UCASE$(A$)
	   CASE "Y"                           'Save the changes
	  ExitCode = 0
	  GOTO OutHere
	   CASE "N"                           'Leave without saving
	  ExitCode = 2
	  GOTO NoSave
	   CASE ELSE                          'Go back for more changes
	  GOTO EditIt
	END SELECT
	  

Del.Items:                                'F7   Delete Row
	FOR X = 20 TO 1
	IF Text$(X) <> "" THEN EXIT FOR
	X = X - 1
	NEXT X
	 
	DelLast = X
	FOR X = Count% TO DelLast - 1
	Text$(X) = Text$(X + 1)
	NEXT X

	Text$(DelLast) = ""
	GOSUB Reprint
	GOTO EditIt

Insert.Items:                             'F8  Insert row
	FOR X = 20 TO Count% STEP -1
	Text$(X + 1) = Text$(X)
	NEXT X
	Text$(Count%) = ""
	GOSUB Reprint
	GOTO EditIt

Reprint:                                  'Print commands in editor
	FOR X = 1 TO 20
	LOCATE 2 + X, 8
	Qprint0 LTRIM$(STR$(X%)), -1
	LOCATE , 11
	Qprint0 SPACE$(60), -1
	Qprint0 Text$(X), -1
	NEXT X
RETURN

OutHere:
	L = 20                                'Find Top valid Text$()
	WHILE Text$(L) = ""
	L = L - 1
	WEND
	IF ExitCode = 1 THEN GOTO NoSave
	IF L = 0 THEN                         'First Item is blank
	   ExitCode = 2
	   GOTO NoSave
	END IF

	FOR X = 1 TO L                        'Check for blank line
	IF Text$(X) = "" THEN
		FOR Y = X TO L - 1
		Text$(Y) = Text$(Y + 1)
		NEXT Y
		Text$(L) = ""
	END IF
	NEXT X

	IF L < 20 THEN                        'Back fill with blanks
	   FOR X = (L + 1) TO 20
	   Text$(X) = ""
	   NEXT X
	END IF

NoSave:
	 
	ScrnRest0 1, 1, 25, 80, SEG SCArray%(2000)

END SUB

SUB GetScrn (ScrName$, Lib(), Flag) STATIC

	LibNo UCASE$(ScrName$), Lib(), N, Flag
	IF Flag THEN EXIT SUB
	StartScr = Lib(N * 11)
	Length = Lib((N * 11) + 1)
	Offset = Lib((N * 11) + 2)
	ScrnRest0 ((Offset \ 160) + 1), ((Offset MOD 160) + 1), (Length \ 80) + (Offset \ 160), (Offset MOD 160) + ((Length - 1) MOD 80) + 1, Lib(StartScr)

END SUB

SUB Help STATIC                         'Loads & displays help file

  ScrnSave0 1, 1, 25, 80, SEG SCArray%(0)

	Row = CSRLIN
	Col = POS(0)
	IF LibFlag THEN GOSUB Help.File     'If help not loaded, load it
	IF NoHelp GOTO No.Help              'If no help file bag out
	IF PreHelp THEN
	   Y = PreHelp
	ELSE
	   Y = 1
	END IF
	
ShowHelp:
	A$ = ""
	FillScrn0 1, 1, 24, 80, 7, 32
	LOCATE 25, 1, 0
	Qprint0 "Hit any key for next or <ESC> to return" + STRING$(41, " "), Colr(2)
	Help1$ = "Help" + LTRIM$(STR$(Y))
	GetScrn Help1$, ScrnArray(), Flag
	IF Flag THEN
	   Y = 1
	   GOTO ShowHelp
	END IF
   
	QGetKey A$, 0
	
	IF A$ = CHR$(27) GOTO Exit.Here     'EXIT SUB
   
	'Ten Help Screens
   
	IF A$ = CHR$(0) + "H" THEN Y = Y - 1 ELSE Y = Y + 1

	GOTO ShowHelp

No.Help:
	CLS
	LOCATE 12, 28
	CALL Chime(Tune%)                        'Sound routine from Pro II
	Qprint0 "Sorry no help available!", Colr(6)
	Tick.Toc 2
	GOTO Exit.Here
	  
Help.File:
	IF NOT Exist%("QMENU.QSL") THEN
	   NoHelp = -1
	   RETURN
	ELSE
	   NoHelp = 0
	END IF

Loadhelp:
	
	PaintBox0 14, 35, 15, 43, Shade%   'Shadow
	LOCATE 13, 34
	Qprint0 " Loading ", Colr(2)
	LOCATE 14, 34
	Qprint0 " Help... ", Colr(2)

	LoadLib "QMENU.QSL", Flag           'Go get our help library
	IF Flag THEN                        ' oops you forgot to put help in
	   NoHelp = -1
	   RETURN
	END IF
	LibFlag = 0                         'Ok library is in memory
	RETURN

Exit.Here:
	LOCATE Row, Col
	   ScrnRest0 1, 1, 25, 80, SEG SCArray%(0)

END SUB

SUB Home.Base STATIC                    'Alerts user if QuickMenu was started
					'the wrong subdirectory
	IF Exist%("QMENU.EXE") THEN EXIT SUB

	FillScrn0 11, 15, 14, 64, Colr(6), 32
	LOCATE 12, 17
	Qprint0 "Please start QuickMenu from its home directory.", Colr(6)
	LOCATE 13, 25
	Qprint0 "Press any key to return to DOS", Colr(6)
	CALL Chime(Tune%)                    'Sound routine from Pro II
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

	LOCATE 22, 10
	Qprint0 "<F1> Help" + SPACE$(38) + "<F3> Shell", Colr(4)
	
	LOCATE 23, 10
	Qprint0 "<F5> Exit to DOS" + SPACE$(31) + "<F10> to Edit", Colr(4)

	IF NOT Homemenu THEN                                'Not Main Menu
	   LOCATE 21, 24                                    'Show how to get back
	   Qprint0 CHR$(17) + " Press <ESC> for Previous Menu " + CHR$(16), Colr(2)
	END IF

END SUB

SUB LibNo (ScrName$, Lib(), N, Flag) STATIC

	N = 0
	Flag = 0
	NScrns = Lib(0)
	Libname$ = SPACE$(8)

	WHILE N < NScrns
	N = N + 1
	TempLen = 8
	FOR p = 1 TO 8
		CTR$ = CHR$(Lib((N * 11) + 2 + p))
		IF CTR$ <> CHR$(0) THEN                     'end of name marker
		   MID$(Libname$, p) = CTR$
		ELSE
		   TempLen = p - 1
		   p = 8
		END IF
	NEXT p
	IF LEFT$(Libname$, TempLen) = ScrName$ THEN EXIT SUB
	WEND

	Flag = 1       'didn't find it

END SUB

SUB LoadLib (Libname$, Flag) STATIC

	IF NOT Exist%(Libname$) THEN
	   Flag = 1
	   EXIT SUB
	END IF

	OPEN Libname$ FOR RANDOM AS #99 LEN = 1     'Check size to dim array
	   Size! = LOF(99)
	CLOSE #99

	Size! = Size! / 2                           '
	REDIM ScrnArray(Size! + 2)
	QBload Libname$, ScrnArray(0)               'Load ScrnArray()

END SUB

SUB LoadLogo (X)

Getlogo:
	IF NOT LibFlag GOTO ShowLogo        'The library is loaded if Libflag = 0
	IF NOT Exist("QMENU.QSL") THEN GOTO AlternateLogo  'If not, then exit
	
	LoadLib "QMenu.QSL", Flag           'FOR INPUT AS #2
	LibFlag = 0                         'Library is loaded now

ShowLogo:
	CLS
	GetScrn "Logo", ScrnArray(), Flag
	QGetKey A$, 0
	EXIT SUB

AlternateLogo:
	CLS
	CALL Box0(11, 21, 15, 60, 1, 64)

	LOCATE 12, 22
	CALL Qprint0("             QuickMenu is             ", 64)
	LOCATE 13, 22
	CALL Qprint0("     Copyright (c) 1989 Jay Munro     ", 64)
	LOCATE 14, 22
	CALL Qprint0(" Copyright (c) 1989 Crescent Software ", 64)
	Tick.Toc 3

END SUB

SUB Log.It (CNT)
	Shade% = Shade% AND 127

	Mix$ = LTRIM$(STR$(Texture%)) + "*" + LTRIM$(STR$(BlankTime%)) + "=" + LTRIM$(STR$(Shade%))
   
	Item$(0, 1) = STR$(CNT)             'Set Number of menu items
	OPEN Current.Menu$ + ".QMU" FOR OUTPUT AS #1
	   PRINT #1, Item$(0, 0)          'Name of Menu
	   PRINT #1, Item$(0, 1)          'Number of items
	   PRINT #1, Mix$

	   FOR X = 1 TO 8
	   CheckColor Colr(X)
	   PRINT #1, STR$(Colr(X))
	   NEXT X

	   FOR Y = 1 TO CNT               'Save Commands
	   PRINT #1, Item$(Y, 22)     'Dos/Menu item flag
	   FOR X = 0 TO 20
		   PRINT #1, Item$(Y, X)
		   IF Item$(Y, X) = "" THEN EXIT FOR
	   NEXT X
	   NEXT Y

	   PRINT #1, CHR$(26);
	   Position% = SEEK(1)
	CLOSE #1

	OPEN Current.Menu$ + ".QMU" FOR BINARY AS #1
	   FOR X = 0 TO CNT
	   IF Pswd$(X) = "" THEN Pswd$(X) = DPW$
	   PUT #1, Position% + (X * 8), Pswd$(X)
	   NEXT X

	   Position% = SEEK(1)
	   IF SysPass$ = "" THEN SysPass$ = DPW$
	   PUT #1, Position%, SysPass$
	CLOSE #1
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

DEFINT A-Z
SUB Password (PWCode%, Level%)
   
	IF Level% = 1 AND Pswd$(Choice) = DPW$ THEN 'No PW exists
	   PWCode% = -1                             'Give the okey dokey
	   EXIT SUB
	END IF

   ScrnSave0 1, 1, 25, 80, SEG SCArray%(2000)
	PreHelp = 9
	SELECT CASE Level%
	   CASE 1                                   'Check password
	  GOSUB CheckState
	  PromptBox
	  GOTO Check.Password
	   CASE 2                                   'Adding stuff
	  GOSUB CheckState
	  GOTO Add.password
	   CASE 3                                   'Editing stuff
	  GOSUB CheckState
	  GOTO Edit.Password
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
	IF A$ = CHR$(0) + CHR$(75) THEN A$ = CHR$(8)  'convert left arrow to backspace
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
	   CASE CHR$(8), CHR$(0) + CHR$(77)         'Backspace
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
		
Add.password:
	LOCATE 23, 20
	Qprint0 "Enter Password ", Colr(4)
	LOCATE 23, 35
	Max = 8
	Caps.On = 0
	TextIn 0, Temp$, Colr%(4)

	IF ExitCode = 2 THEN
	   PWCode = 0
	   EXIT SUB
	END IF

	Temp.Pswd$ = Temp$
	PWCode = -1
   
	IF Temp.Pswd$ = "" THEN
	   Temp.Pswd$ = DPW$
	   GOTO Exit.Password
	END IF

	GOSUB Encoding
	GOTO Exit.Password

Edit.Password:
	LOCATE 23, 20
	Qprint0 "Edit Password ", Colr(4)
	LOCATE 23, 35
	Max = 8
	Caps.On = 0
	TextIn 0, Temp$, Colr%(4)
   
	IF ExitCode = 9 THEN
	   Temp.Pswd$ = DPW$
	   GOTO Exit.Password
	END IF
   
	IF Temp$ = "" GOTO Exit.Password            'User pressed Enter
   
	IF ExitCode = 2 THEN                        'User pressed Escape
	   PWCode = 0
	   EXIT SUB
	END IF

	Temp.Pswd$ = Temp$
	GOSUB Encoding
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
	   CASE 2
	  PromptBox
	  GOTO EditSysPw
	   CASE ELSE
	  GOTO Exit.Password
	END SELECT

PutSysPw:
	OPEN "MENU.QMU" FOR BINARY AS #1             'put password same as above
	   LN% = LOF(1)                              'get end of file
	   PUT #1, LN% - 7, SysPass$                 'back up and fill in
	CLOSE #1
	GOTO Exit.Password
   
EditSysPw:
	Promptline " <Enter> for no change   <ESC> - Cancel   <F7> - delete password "
	LOCATE 22, 20
	Qprint0 "New System Password:", Colr(4)
	LOCATE 22, 42
	Max = 8
	Caps.On = 0
	TextIn 0, Temp$, Colr%(4)
	IF ExitCode = 9 THEN
	   SysPass$ = DPW$
	   GOTO PutSysPw
	END IF

	IF Temp$ = "" GOTO Exit.Password

	IF ExitCode = 2 THEN
	   PWCode = 0
	   EXIT SUB
	END IF

	Temp.Pswd$ = Temp$
	GOSUB Encoding
	SysPass$ = Temp.Pswd$
	GOTO PutSysPw

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

DEFINT A-Z
SUB Promptline (A$)

	X = LEN(A$) / 2                 'Get length of message
	B = 36 - X                      'Get padding length
	LOCATE 21, 3
	Qprint0 STRING$(B, Texture%) + CHR$(17) + " " + STRING$(LEN(A$), " ") + " " + CHR$(16) + STRING$(B, Texture%), Colr(2)
	LOCATE , B + 5
	Qprint0 A$, Colr(2)  'OR 128    'Un rem this to flash message


END SUB

DEFSNG A-Z
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
	   CALL Chime(Tune%)                        'Sound routine fromPro II
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
	User.Inp$ = ""
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
   
	IF RepChar$(Rep%) = "" AND NOT DidAsk%(Rep%) THEN  'If we haven't
	   LOCATE ULR% + 1, ULC% + 2                   ' made the variable
	   Max% = 50                                   ' then lets make it
	   Caps.On% = 0
	   TextIn 0, RepChar$(Rep%), Colr%(4)  'get users input
		 IF ExitCode = 2 THEN              'user hit escape
		FOR X% = 0 TO 9
			DidAsk%(X%) = 0            'erase flags
			RepChar$(X%) = ""          'and everything
		NEXT X%
		EXIT SUB
		 END IF
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
	IF Exist%("$$HELL.BAT") THEN CALL KillFile("$$HELL.BAT")  'kill our batch file

END SUB

DEFINT A-Z
SUB SpltColr (Colr, FG, BG)
FG = Colr MOD 16
BG = Colr \ 16

END SUB

SUB TextIn (F%, T$, EditColr%)           'Text input routine

	SpltColr EditColr, FG, BG
	IF MonType1% THEN                    'determine monitor type
	   Clr = 0                           'color
	ELSE
	   Clr = 1                           'mono
	END IF

	X$ = T$                              'X$ is a working copy of input string
	ExitCode = 0: QMInsert = 0: Curpo = 1 'initialize flags

	Length = LEN(X$)
	IF Length > Max THEN EXIT SUB        'already to big to edit

	X$ = X$ + SPACE$(Max - Length)
	COLOR FG, BG
	PRINT X$;

	IF Max > 1 THEN                      'put a ® to signal end of line
	   PRINT "®";
	   Exitpos = POS(0) - 1
	   LOCATE , POS(0) - (Max + 1), 1
	ELSE
	   LOCATE , POS(0) - Max, 1          'put the cursor at the beginning
	END IF
	
	GOSUB T2Insert.Off                   'set cursor size according to display
   
T2Get.Key:
	IF Curpo > Length AND QMInsert <> 0 THEN GOSUB T2Insert.Off                 'disallow insert if cursor past end
	IF Curpo > Max GOTO T2Enter          'field is filled, handle as Enter key
	'QGetKey A$, -1
	A$ = INKEY$
	IF A$ = "" GOTO T2Get.Key
	IF LEN(A$) = 1 GOTO T2Regular.Key

	A$ = RIGHT$(A$, 1)                  'it was an extended key, get the code

	ON INSTR("GKMORSHP;", A$) GOTO T2Home, T2Left, T2Right, T2EndKey, T2Ins, T2Del, TUp, T2Enter, THelp
   
	IF F% THEN GOTO T2Get.Key           'filter out function keys

	ON INSTR("=>@<", A$) GOTO T2Message, T2EndMessage, T2UserInput, T2NoReturn
	ON INSTR("ABCqp", A$) GOTO T2InsertLine, T2deleteLine, T2Alert, T2Import, T2Export
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
	   GOTO T2Get.Key                   'Insert is already on, turn it off
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
	MID$(X$, A, 1) = MID$(X$, A - 1, 1)
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
   
THelp:                                  'F1 Help
	Help
	LOCATE , , 1
	GOTO T2Get.Key

T2NoReturn:                             'F2 No return to Qmenu
	A$ = "ê"
	GOTO T2Regular.Key

T2Message:                              'F3 Start Message
	A$ = "µ"
	GOTO T2Regular.Key
   
T2EndMessage:                           'F4 End Message
	A$ = "Æ"
	GOTO T2Regular.Key
   
T2UserInput:                            'F6 User input
	A$ = "û"
	GOTO T2Regular.Key

T2Alert:                                'F9  Beep
	A$ = "ë"
	GOTO T2Regular.Key

T2Import:
	ExitCode = 20
	GOTO T2Enter

T2Export:
	ExitCode = 19
	GOTO T2Enter

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

T2InsertLine:                           'F8 insert a line in editor
	ExitCode = 9
	GOTO T2Enter
   
T2deleteLine:                           'F7 delete a line in editor
	ExitCode = 10
	GOTO T2Enter

T2Insert.Off:                           'clear Insert mode and restore cursor,
					'  depending on MonType
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
	   CALL KillFile("Trail")           'then kill the dude
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

DEFINT A-Z
SUB Zero.Out (X$)

	FOR X = 1 TO LEN(X$)                'Name, replace with underscore
	Z = INSTR(X$, " ")
	IF Z THEN MID$(X$, Z, 1) = "_"
	NEXT X

END SUB

