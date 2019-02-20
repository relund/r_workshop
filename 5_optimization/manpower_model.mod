/*

Manpower planning in the logistics section

Author: (c) Lars Relund Nielsen 

Coding/naming convention
------------------------ 
- Language: English.
- We use CamelCase (https://en.wikipedia.org/wiki/Naming_convention_(programming)).
- Starting with upper case: sets, arrays (ending with s e.g. DayTypes).
- Starting with lower case: elements in sets, tuple.
- Primary binary variables start with x.
- Primary integer variables start with y.
- Primary continous variables start with z.

Assumptions
-----------
- Each course with a teaching activity must have an Exam activity 
  That is, if combine teaching and exam in one activity then the type must be Exam
- Activities must be disjoint.
- An activity can only be run at most once a year (implying a seq of the same activity can be sorted by year)
- At most 10 activities per course (big M)
**/

// set options directly in this file so can use oplrun
execute
{
  cplex.epgap = 0.015;	// relative gap 
  cplex.tilim = 300;	// time limit in sec
  cplex.solnpoolcapacity = 5;  // sol pool of 5
  cplex.solnpoolreplace = 2;
}


tuple person {
	key string abbrv;
	//string fullName;
};

tuple course { 	// could also be admin in general
	key string name;
	int semester;  // either 1 = Spring or 2 = Autum
	int mandatory; // 1/0 = yes/no		
};

tuple activity {		// can be seen as a timeslot we have to allocate a person(s)
	key course c;
	key int year;
	string type;  		// activity type, one of {"Teaching", "Exam", "Supervison", "Admin"};
	key string name;	// activity name
	float norm;			// norm for activity
	float unitNorm; 	// norm for one unit e.g. single teaching module, one exam, one supervision (norm and unitNorm may not be the same for grading)
	int split;			// can norm be split (e.g. if written exams)
	float minNorm;		// min norm if can split
	int minSeq;			// min number of times the activity must be repeated
};

tuple activityPersonPair {   
	key activity a;
	key person p;
	int cost;
};

tuple activityPersonPairValue {   
	key activityPersonPair ap;
	float value;
};

tuple cAPComb {		// course, activitiy name and person combinations
	key string cName;	// course name
	key string aName;	// activity name
	key string pName;   // person
	int minSeq;		// min number of times the activity must be repeated
};

tuple timeUnit {
	key int year;
	key int semester;
};

{activityPersonPair} ActivityPersonPairs = ...;		// set of possible allocations of a person to an activity (includes cost)
{activity} Activities = { ap.a | ap in ActivityPersonPairs};
{course} Courses = { a.c | a in Activities};
{course} ElectiveCourses = { c | c in Courses : c.mandatory == 0 };
{activity} SplitActivities = { a | a in Activities : a.split == 1 };
{activity} NoSplitActivities = { a | a in Activities : a.split == 0 };
{activityPersonPair} SplitActivityPersonPairs ={ ap | ap in ActivityPersonPairs : ap.a.split == 1 };
{activityPersonPair} NoSplitActivityPersonPairs ={ ap | ap in ActivityPersonPairs : ap.a.split == 0 };
//{activity} SupervisionActivities = { a | a in Activities : a.type == "Supervision" };
//{activity} TeachingActivities = { a | a in Activities : a.type == "Teaching" };
//{activity} ExamActivities = { a | a in Activities : a.type == "Exam" };
sorted {int} Years = { a.year | a in Activities};	// time horizon under consideration
{person} Persons = { ap.p | ap in ActivityPersonPairs};
float Norms[Persons][Years] = ...;	// norms for each year 
float Saldos[Persons] = ...;   // primo TPU saldo 
int TeachSeqs[Persons] = ...;	// sequence constraints valid, 1 = yes, 0 = no
{activityPersonPair} FixedXDoActivity = ...;	// activities that are fixed to a person (might still be split)
{activityPersonPairValue} MinYSplitActivity = ...;	// min values of ySplitActivity (use ap.cost to store value)
{activityPersonPairValue} MaxYSplitActivity = ...;	// max values of ySplitActivity (use ap.cost to store value)
sorted {timeUnit} TimeUnits = {<ap.a.year, ap.a.c.semester> | ap in ActivityPersonPairs}; 
{activityPersonPair} SeqActivityPersonPairs = {ap | ap in ActivityPersonPairs : ap.a.minSeq > 1 && TeachSeqs[ap.p] == 1 };		//&& ap.a.type == "Teaching"
//{cAPComb} CAPCombs = { <ap.a.c.name, ap.a.name, ap.p.abbrv, ap.a.minSeq> | ap in ActivityPersonPairs};  //: ap.a.minSeq > 1 && TeachSeqs[ap.p] == 1
//{cAPCombYear} CAPCombYears = { < <ap.a.c.name, ap.a.name, ap.p.abbrv, ap.a.minSeq>, ap.a.year > | ap in ActivityPersonPairs };		//: ap.a.minSeq > 1 && TeachSeqs[ap.p] == 1 
//{cAPComb} CAPTeachCombs = { <ap.a.c.name, ap.a.name, ap.p.abbrv, ap.a.minSeq> | ap in ActivityPersonPairs : ap.a.type == "Teaching" };  
{cAPComb} CAPSeqCombs = { <ap.a.c.name, ap.a.name, ap.p.abbrv, ap.a.minSeq> | ap in SeqActivityPersonPairs};  
sorted {int} CAPCombYearSets[cc in CAPSeqCombs] =   // CAPCombs union 
	{ap.a.year | ap in SeqActivityPersonPairs : ap.a.c.name == cc.cName && ap.a.name == cc.aName && ap.p == <cc.pName>}; 


assert {	// Check data
	// Do all courses with teaching have an exam?
	forall (c in Courses, y in Years, p in Persons) {
		chk1: ( sum(ap in ActivityPersonPairs: ap.p == p && ap.a.year == y && ap.a.c == c && ap.a.type == "Teaching") 1 > 0 
		? sum(ap in ActivityPersonPairs: ap.p == p && ap.a.year == y && ap.a.c == c && ap.a.type == "Exam") 1 > 0
		: 0 == 0);
	}
	// Activities have same minSeq
	/*forall (cap in CAPSeqCombs) {
		chk2: sum(ap in SeqActivityPersonPairs : ap.a.c.name == cap.cName && ap.a.name == cap.aName && ap.p.abbrv == cap.pName ) 1 == 1;
	}*/		
}


//// Variables
dvar boolean xDoActivity[ActivityPersonPairs];		    // Equals 1 if person do activity
dvar boolean xDoElective[ElectiveCourses];				// Equals 1 if run the elective
dvar int+  ySplitActivity[SplitActivityPersonPairs];	// Number of times that do the unit norm 
dvar float zSaldo[Persons][Years];						// Ultimo TPU saldo a given year 
dvar float+ dOverRibbon[Persons][Years];				// TPU over ribbon ub
dvar float+ dUnderRibbon[Persons][Years];				// TPU under ribbon lb
dvar float+ dOverMinSeq[SeqActivityPersonPairs];			// Over min seq given start in year 
dvar boolean xStartActivity[SeqActivityPersonPairs];
 
//constraint tmp[SeqActivityPersonPairs];
//constraint tmp2[SeqActivityPersonPairs];
 
//// Model 
minimize sum(ap in NoSplitActivityPersonPairs) xDoActivity[ap] * ap.cost * ap.a.norm
	+ sum(ap in SplitActivityPersonPairs) ySplitActivity[ap] * ap.cost * ap.a.unitNorm
	+ sum(p in Persons, y in Years) (dOverRibbon[p, y] * 15 * 0.65^(ord(Years,y)) + dUnderRibbon[p, y] * 30 * 0.65^(ord(Years,y)) )
	//+ sum(c in ElectiveCourses) (1 - xDoElective[c]) * 100
	+ sum(ap in SeqActivityPersonPairs) dOverMinSeq[ap] * 500
;

 
subject to { 
	//// Fixed or bounds on variables
	forall (ap in FixedXDoActivity) { 
		xDoActivity[ap] == 1;	
	}
	forall (apv in MinYSplitActivity) { 
		ySplitActivity[apv.ap] >= apv.value;	
	}
	forall (apv in MaxYSplitActivity) { 
		ySplitActivity[apv.ap] <= apv.value;	
	}
		
	
	//// Sabbatical
	// If have sabbatical then can not teach courses that semester
	forall (ap in ActivityPersonPairs : ap.a.type == "Sabbatical")  {
	 	sum(app in ActivityPersonPairs : app.a.year == ap.a.year && app.a.c.semester == ap.a.c.semester && app.p == ap.p) 
	 		xDoActivity[app] <= (1 -xDoActivity[ap]) * 100 + 1;
	}
	// Can only do one sabbatical in the planing period (assume not to long)
	forall (p in Persons)  {
	 	sum(ap in ActivityPersonPairs : ap.a.type == "Sabbatical" && ap.p == p) xDoActivity[ap] <= 1;
	}
	
	
	//// Max TPU in a semester
	forall (p in Persons, t in TimeUnits)  {
	 	sum(ap in NoSplitActivityPersonPairs : ap.p == p && ap.a.year == t.year && ap.a.c.semester == t.semester) xDoActivity[ap] * ap.a.norm
	 	+ sum(ap in SplitActivityPersonPairs : ap.p == p && ap.a.year == t.year && ap.a.c.semester == t.semester) ySplitActivity[ap] * ap.a.unitNorm
	 	<= 540;
	}


	//// Mandatory course
	// Activity can be done by exactly one person
	forall (a in NoSplitActivities : a.c.mandatory == 1) {
		sum(ap in NoSplitActivityPersonPairs : ap.a == a) xDoActivity[ap] == 1;	
	}
	// If split then number of times must equal demand of units
	forall (a in SplitActivities : a.c.mandatory == 1) {
		sum(ap in SplitActivityPersonPairs : ap.a == a) ySplitActivity[ap] == ceil(a.norm/a.unitNorm);	
	}
	
	
	//// Elective course
	// If no split then activity can only be done by one person and only if run
	forall (a in NoSplitActivities : a.c.mandatory == 0) {
		sum(ap in NoSplitActivityPersonPairs : ap.a == a) xDoActivity[ap] == xDoElective[a.c];	
	}
	// If split then number of times must equal demand of units if run
	forall (a in SplitActivities : a.c.mandatory == 0) {		
		sum(ap in SplitActivityPersonPairs : ap.a == a) ySplitActivity[ap] == ceil(a.norm/a.unitNorm) * xDoElective[a.c];	
	}
	// If elective doesnt run then no activities (at most 10 activities if run)
	forall (c in ElectiveCourses) {
		sum(ap in NoSplitActivityPersonPairs: ap.a.c == c) xDoActivity[ap] <= xDoElective[c] * 10;
	}

	// If do activity then do at least the minimum TPU amount (x=1 => y>min TPU)
	forall (ap in SplitActivityPersonPairs) { 
		ySplitActivity[ap] >= ap.a.minNorm/ap.a.unitNorm * xDoActivity[ap];
	}
	// If y positive then x = 1 (x=0 => y=0) (y <= max times)
	forall (ap in SplitActivityPersonPairs) { 
		ySplitActivity[ap] <= xDoActivity[ap] * ceil(ap.a.norm/ap.a.unitNorm);
	}
	// If a given person a given year teach in a course then also do a part of the exam
	forall (c in Courses, y in Years, p in Persons) {
		sum(ap in ActivityPersonPairs: ap.p == p && ap.a.year == y && ap.a.c == c && ap.a.type == "Teaching") xDoActivity[ap] 
			<= 10 * sum(ap in ActivityPersonPairs: ap.p == p && ap.a.year == y && ap.a.c == c && ap.a.type == "Exam") xDoActivity[ap];
	}

	//// TPU saldos
	// First year
	forall (p in Persons, y in {first(Years)}) { 
		zSaldo[p][y] == Saldos[p] 
			+ sum(ap in NoSplitActivityPersonPairs : ap.a.year == y && ap.p == p) xDoActivity[ap] * ap.a.norm
			+ sum(ap in SplitActivityPersonPairs : ap.a.year == y && ap.p == p) ySplitActivity[ap] * ap.a.unitNorm
			- Norms[p][y];
	}
	// Remaining years
	forall (p in Persons, y in Years diff {first(Years)}) { 
		zSaldo[p][y] == zSaldo[p, prev(Years, y)] 
			+ sum(ap in NoSplitActivityPersonPairs : ap.a.year == y && ap.p == p) xDoActivity[ap] * ap.a.norm
			+ sum(ap in SplitActivityPersonPairs : ap.a.year == y && ap.p == p) ySplitActivity[ap] * ap.a.unitNorm
			- Norms[p][y];
	}	
	// TPU ribbon
	forall (p in Persons, y in Years) { 
		zSaldo[p][y] - dOverRibbon[p][y] <= 200;
		zSaldo[p][y] + dUnderRibbon[p][y] >= 0;
	}

	
	////Same activity in sequence 
	// If first time then equal 1
	forall (ap in SeqActivityPersonPairs, t in {ord(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], ap.a.year)}) { 		
		xStartActivity[ap]
			>= ( t == 0 ?   
				xDoActivity[ap] : 
				xDoActivity[ap] 
				- xDoActivity[< <ap.a.c, item(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], t-1), ap.a.name>, ap.p >] );
	}
	// At least minSeq activities in a row
	forall (ap in SeqActivityPersonPairs : 
		ord(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], ap.a.year) <= card(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >]) - 2,  
		t in {ord(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], ap.a.year)} ) 
	{ 		
		sum(k in t..(minl(card(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >]) - 1, t + ap.a.minSeq - 1) ) )
		xDoActivity[< <ap.a.c, item(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], k), ap.a.name>, ap.p >]  
		>= xStartActivity[ap] * minl(card(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >]) - t, ap.a.minSeq);
	}
	// Times over minSeq
	forall (ap in SeqActivityPersonPairs : 
		ord(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], ap.a.year) <= card(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >]) - 1 - ap.a.minSeq,
		t in {ord(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], ap.a.year)} ) 
	{ 		
		sum(k in t..(t + ap.a.minSeq) ) 
		xDoActivity[< <ap.a.c, item(CAPCombYearSets[< ap.a.c.name, ap.a.name, ap.p.abbrv >], k), ap.a.name>, ap.p >] - dOverMinSeq[ap] 
		<= ap.a.minSeq;	// count each time a period has a seq longer than minSeq
	}	
	// xStartActivity = 1 => xDoActivity = 1
	forall (ap in SeqActivityPersonPairs) xStartActivity[ap] <= xDoActivity[ap];
	

	//// Hack to debug
	//forall (cap in CAPCombYears1)	
	//	1 == 1;
};






/// Postprocessing

tuple solution {
	key int year;
	key int semester;
	key string course;
	key string activity;
	key string person;
	float tpu;
	float cost;
	int mandatory;
	string type;
};

{solution} NoSplitSolutions = {<
	ap.a.year,
	ap.a.c.semester,
	ap.a.c.name,
	ap.a.name,
	ap.p.abbrv,
	ap.a.norm,
	ap.cost * ap.a.norm,
	ap.a.c.mandatory,
	ap.a.type
> | ap in NoSplitActivityPersonPairs : xDoActivity[ap] == 1 && ap.a.split == 0
};

{solution} SplitSolutions = {<
	ap.a.year,
	ap.a.c.semester,
	ap.a.c.name,
	ap.a.name,
	ap.p.abbrv,
	ySplitActivity[ap] * ap.a.unitNorm,
	ap.cost * ySplitActivity[ap] * ap.a.unitNorm,
	ap.a.c.mandatory,
	ap.a.type
> | ap in SplitActivityPersonPairs : xDoActivity[ap] == 1 && ySplitActivity[ap] > 0  && ap.a.split == 1
};

sorted {solution} OutSolutions = NoSplitSolutions union SplitSolutions;

tuple saldo {
	key int year;
	key string person;
	float tpu;
};

sorted {saldo} OutSaldos = {<
	y,
	p.abbrv,
	zSaldo[p, y]
> | p in Persons, y in Years};

execute POST_PROCESS {
	var f = new IloOplOutputFile("solution_0.csv");		// open file for writing
	f.writeln("Year;Sem;Course;Activity;Person;TPU;Cost;Mandatory;Semester;Type");	
	for (var s in OutSolutions) {
		f.writeln(s.year, ";", s.semester, ";", s.course, ";", s.activity, ";", s.person, ";", s.tpu, ";", s.cost, ";", s.mandatory, ";", s.semester, ";", s.type);		
	}
	f.close();	// close file
	
	var f = new IloOplOutputFile("saldo_0.csv");		// open file for writing
	f.writeln("Year;Person;TPU Saldo");	
	for (var s in OutSaldos) {
		f.writeln(s.year, ";", s.person, ";", s.tpu);		
	}
	f.close();	
};

