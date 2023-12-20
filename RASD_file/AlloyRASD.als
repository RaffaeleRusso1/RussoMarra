//Definition of the Student
sig Student {
}

//Definition of the Educator
sig Educator {
}

//Definition of the Tournament
sig Tournament {
	   creator: one Educator,                     //Tournament creator
	   invitedEducators: set Educator,         //Educators invited into the tournament
	   participantEducators: set Educator,   //Invited educators who wanted to participate in the tournament
	   Battles: disj some Battle,                 //The battles within the tournament are all different from each other 
	   participantStudents: set Student      //Students participating in the tournament
} 

//Definition of the Battle
sig Battle {
 	 creator: one Educator,                       //Battle creator
  	 participantTeams: set Team,              //Teams participating in the battle
	 evaluator: disj one Evaluator,             //Each battle has a different evaluator
	 has: disj one FinalRankingBattle         //Each battle has its own final ranking
}

//Definition of the Team
sig Team {
	 creator: one Student,                         //Team creator
	 members: set Student,                       //Team members
	 push: disj set Project,                        //Each team has various projects pushed
	 lastPush: disj lone LastProject             //Each team has the latest project pushed
}

//Definition of the Evaluator
sig Evaluator{
	configurator: one Educator                 //The educator configuring the evaluator
} 

//Abstract definition of a project
abstract sig Proje {
	 rated: one Evaluator,                         //Any project is evaluated by 1 Evaluator
	 has: disj one Score                           //Each project has its own score
}

//Definition of a Project
sig Project extends Proje{

}

//Definition of a LastProject
sig LastProject extends Proje{
	 manualEvaluation: lone Educator          //The last project unlike others may also have a manual evaluation by the educator.
}

//Definition of a Score 
sig Score {
}

//Definition of a FinalRankingBattle
sig FinalRankingBattle{
	 basedOn: set Score                        //The final battle ranking is based on the scores 
}


//All final battle rankings have a battle in which the following participate
fact EachFinalRankingBelongsToBattle{
all rb: FinalRankingBattle | one b: Battle | rb in b.has 
}


// The final battle ranking is based on the scores of the last projects pushed 
fact FinalRankingBasedOnScores{
all rb: FinalRankingBattle, b: Battle | rb in b.has implies  rb.basedOn =  b.participantTeams.lastPush.has 
}


//Evaluator can only be configured by the creator of the battle where the team participates 
fact EvaluatorConf{
	all ev: Evaluator, b: Battle | ev in b.evaluator implies ev.configurator = b.creator
}

//A team's pushed project is evaluated by the evaluator who has the battle where the team is enrolled
fact ProjectRated{
	all p: Proje, tm: Team,  b: Battle | tm in b.participantTeams and (p in tm.push or p in tm.lastPush) implies p.rated =  b.evaluator
}

//The educator who created the battle can decide whether or not to do manual evaluation of the teams' latest projects 
fact SameManualEvaluationInBattle {
  all b: Battle |
      all lp1, lp2: LastProject |
        (lp1 in b.participantTeams.lastPush and lp2 in b.participantTeams.lastPush) implies
          lp1.manualEvaluation = lp2.manualEvaluation or no lp1.manualEvaluation 
}

//This facts allows us to say that if one team has the last project delivered the others will have it too because the battle will be over
fact LastProjectConsistency {
 all b: Battle | #b.participantTeams.lastPush > 0 implies #b.participantTeams =  #b.participantTeams.lastPush
}


//All the latest projects have a Team where the following are included.
fact LastProjectInTeam{
all p: LastProject | one tm: Team|  p in tm.lastPush
}

//All the projects have a Team where the following are included.
fact ProjectInTeam{
all p: Project | one tm: Team|  p in tm.push
}

//All the scores have a project where the following are included.
fact ScoreInProje{
all sc: Score | one pj: Proje | sc in pj.has
}

//All the Evaluator have a Battle where the following are included.
fact EvaluatorInBattle{
all e: Evaluator | one b: Battle|  e in b.evaluator
}

//All the Battle have a Tournament where the following are included.
fact BattleInTournament{
all b: Battle | one t: Tournament|  b in t.Battles
}

//All the Team have a Battle where the following are included.
fact TeamInBattle{
all tm: Team | one b: Battle|  tm in b.participantTeams
}

//A battle in the tournament implies that the creator of the battle must be part of the tournament educators and the participants of the battle must be part of the tournament
fact EachBattleBelongsToOneTournament {
  all t: Tournament, b: Battle |
    (b in t.Battles) implies (b.creator in t.participantEducators and b.participantTeams.members in t.participantStudents)
}

//A team can only participate in one battle at a time 
fact TeamBattaglia {
all disj b1, b2: Battle, tm: Team | tm in b1.participantTeams implies tm not in b2.participantTeams
}

// Each team has some students within
fact StudentCanParticipateInOneTeam {
  all tm: Team | some s: Student | s in tm.members
}

//A student may participate in one team at a time
fact NoDuplicateStudentAcrossTeam {
  all disj t1, t2: Team, s: Student | s in t1.members implies s not in t2.members
}


//The creator educator is part of the tournament participants
fact CreatorPartecipate {
  all t: Tournament, e: Educator | e in t.creator implies e in t.participantEducators and e not in t.invitedEducators
}

//Only invited eductors can be participants 
fact OnlyInvitedEducatorsCanParticipate {
  all t: Tournament, e: Educator | e in t.participantEducators and e not in t.creator implies e in t.invitedEducators
}


//All educators participating in the tournament create at least one battle 
fact EducatorParticipatesInBattleCreateAtLeastOneBattle {
  all e: Educator, t: Tournament |
    e in t.participantEducators implies some b: Battle | b in t.Battles and b.creator = e
}


//The creator of a team is part of the members of the same team
fact CreatorIsMemberOfTeam {
  all tm: Team | tm.creator in tm.members
}




//A general scenerio of the system
pred createScenario {
	#Educator = 2

	#Student = 5

	#Tournament = 1

	#Battle = 2

	#Team = 3

	#LastProject > 1

	#Project > 1
}


run createScenario for 5












