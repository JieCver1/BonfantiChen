//----------------------------------------------------------------------------------------------------------------------------------
//---------------------------- RASD Alloy Dynamic Model ----------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------
//---------------------------------- Signatures ------------------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------

abstract sig User {}                            // Abstract signature for all users

sig Student extends User {                      // Student signature to model students' submitted applications and participations in internships
    var submits: set Application,               // Applications submitted by student
    var participates: set Internship            // Internships student has participated in
}{
    one u: University | this in u.enrolls       // Fact to ensure that each student is enrolled in one and only one university
}

sig Company extends User {                      // Company signature to model companies' published internships
    var publishes: set Internship               // Internships published by company
}

sig University extends User {                   // University signature to model universities' students
    var enrolls: set Student                    // Students enrolled in university
}

var sig Internship {                            // Internship signature to model internships' applications and feedbacks
    var submissions: set Application,           // Applications submitted by students for internship
    var submittedFeedbacks: set Feedback,       // Feedbacks submitted by students who participated in internship
    var internStatus: one InternshipStatus      // Status of internship
}{
    one c: Company | this in c.publishes        // Fact to ensure that each internship is published by one and only one company
}             

var sig Application {                           // Application signature to model applications' interviews
   var interview: lone Interview,
   var AppStatus: one ApplicationStatus         // Interview scheduled for application
}{
    one s: Student | this in s.submits          // Fact to ensure that each application is submitted by one and only one student
    one i: Internship | this in i.submissions   // Fact to ensure that each application is submitted for one and only one internship
}

var sig Feedback {} {                           // Feedback signature to model feedbacks submitted by students who participated in internships and companies who published them
    one i: Internship | this in i.submittedFeedbacks    //Fact to ensure that each feedback is submitted for one and only one internship
} 

var sig Interview {}  {                         // Interview signature to model interviews scheduled for applications
    one a: Application | this in a.interview    //Fact to ensure that each interview is scheduled for one and only one application
}

/*
Model the status of an application:
SubmissionWaiting --> the application has been submitted by the student and is waiting for the response from the company
SelectedToInterview --> the application has been selected by the company for an interview
AcceptedToInternship --> the application has been accepted by the company
AcceptedOffer --> the internship has been accepted by the student when the company has sent the offer
RejectedOffer --> the internship has been rejected by the student when the company has sent the offer
Rejected --> the application has been rejected by the company
*/
abstract sig ApplicationStatus{}
one sig SubmissionWaiting, SelectedToInterview, AcceptedToInternship, 
        AcceptedOffer,     RejectedOffer,       Rejected                 extends ApplicationStatus{}


/*
Model the  status of internship:
InPublishing --> the company is published the internship and is open for applications
InSelection --> the company is selecting the students for the internship and after that he accepts or rejects the applications
InProgress --> the students has accepted the offer and the internship started
Completed --> the internship is completed
*/
abstract sig InternshipStatus{}
one sig InPublishing, InSelection, InProgress, Completed extends InternshipStatus{}


//----------------------------------------------------------------------------------------------------------------------------------
//-------------------------- Facts for the dynamic model ---------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------

//Facts used before in Static model 

// Fact to ensure that a student cannot submit multiple applications for the same internship
fact noRepeatedApplicationsForSameInternship{
   always (all s: Student, i: Internship | no disj a1,a2: s.submits | (a1 in i.submissions and a2 in i.submissions) )
}

// Fact to ensure that a feedback is submitted only if at least a student has participated in the internship
fact feedbackOnlyIfStudentInInternship{
    always( all f: Feedback, i: Internship | f in i.submittedFeedbacks 
     implies (some s: Student | i in s.participates and 
        (some a: Application | a in s.submits and a in i.submissions))
    )
}

// Fact to ensure that all internships where a student has participated have an interview scheduled for the application
fact allStudentInternshipsHaveInterviewInApplication{
    always( all s: Student, i: Internship | i in s.participates implies 
        (some a: Application | a in s.submits and a in i.submissions and
        (some intv: Interview | intv in a.interview))
    )
}


//Facts for the dynamic model

// Application can only be in one status at a time
fact ApplicationStatusCanOnlyHaveOnePhaseAtATime{
    always all a: Application | (one a.AppStatus and
    (a.AppStatus = SubmissionWaiting or 
    a.AppStatus = SelectedToInterview or 
    a.AppStatus = AcceptedToInternship or 
    a.AppStatus = AcceptedOffer or 
    a.AppStatus = Rejected or 
    a.AppStatus = RejectedOffer))
}

//Internship can only be in one possible status at a time
fact InternshipStatusCanOnlyHaveOnePhaseAtATime {
    always all i: Internship | one i.internStatus and 
    (i.internStatus = InPublishing or
    i.internStatus = InSelection or
    i.internStatus = InProgress or
    i.internStatus = Completed)
}


/*
If an internship is InPublishing status, all applications in the internship should be in SubmissionWaiting status
If an internship is InSelection status, all applications in the internship should be in SelectedToInterview or Rejected or AcceptedToInternship status
If an internship is InProgress status, all applications in the internship should be in AcceptedOffer or Rejected or RejectedOffer status and at least one application should be in AcceptedOffer status
If an internship is in Completed status, all applications in the internship should be in AcceptedOffer or Rejected or RejectedOffer status and at least one application should be in AcceptedOffer status
*/
fact allowedAppStatusInEachInternshipStatus {
    always( all i: Internship | 
        (i.internStatus = InPublishing implies 
            (all a: i.submissions | a.AppStatus = SubmissionWaiting)) and 
        (i.internStatus = InSelection implies 
            (all a: i.submissions | a.AppStatus = SelectedToInterview or a.AppStatus = Rejected or a.AppStatus = AcceptedToInternship)) and
        (i.internStatus = InProgress implies 
            (all a: i.submissions | a.AppStatus = AcceptedOffer or a.AppStatus = Rejected or a.AppStatus = RejectedOffer) and (some a: i.submissions | a.AppStatus = AcceptedOffer)) and 
        (i.internStatus = Completed implies  
            (all a: i.submissions | a.AppStatus = AcceptedOffer or a.AppStatus = Rejected or a.AppStatus = RejectedOffer) and (some a: i.submissions | a.AppStatus = AcceptedOffer))
    )
}

// Variation of Interview in every state of the application
fact InterviewInEveryStateOfApplication{
    always all a: Application | 
    (a.AppStatus = SubmissionWaiting implies a.interview = none) and
    (a.AppStatus = SelectedToInterview implies a.interview != none) and
    (a.AppStatus = AcceptedToInternship implies a.interview != none) and
    (a.AppStatus = AcceptedOffer implies a.interview != none) and
    (a.AppStatus = RejectedOffer implies a.interview != none) and
    ((a.AppStatus = Rejected and a.interview != none) implies after always a.interview != none) and
    ((a.AppStatus = Rejected and a.interview = none) implies after always a.interview = none)
}

// When an interview is scheduled for an application, it should never be removed
fact InInterviewCanNotBeRemoved{
    always all a: Application | a.interview != none implies (a.interview' = a.interview)
}



// Student cannot change the university that he is enrolled in
fact studentUniversityInvariant{
    always (all s: Student, u:University | s in u.enrolls implies (after always s in u.enrolls))
}

// Internship cannot change the company that published it
fact internshipCompanyInvariant{
    always (all i: Internship, c:Company | i in c.publishes implies (after always i in c.publishes))
}

// Application cannot change the student that submitted it
fact applicationStudentInvariant{
    always (all a: Application, s:Student | a in s.submits implies (after always a in s.submits))
}

// Student cannot remove the internship that he has participated in
fact studentInternshipInvariant{
    always (all s: Student, i:Internship | i in s.participates implies (after always i in s.participates))
}

// Application cannot change the internship that it is submitted for
fact applicationInternshipInvariant{
    always (all a: Application, i:Internship | a in i.submissions implies (after always a in i.submissions))
}

//Feedback cannot change the internship that it is submitted for
fact feedbackInternshipInvariant{
    always (all f: Feedback, i:Internship | f in i.submittedFeedbacks implies (after always f in i.submittedFeedbacks))
}



// Fact to describe the possible status evolution of the internship
fact internshipStatusAllowedEvolution {
    always( no i: Internship | 
        i.internStatus = InPublishing and (i.internStatus' = InProgress or i.internStatus' = Completed)
        or
        i.internStatus = InSelection and (i.internStatus' = InPublishing or i.internStatus' = Completed)
        or
        i.internStatus = InProgress and (i.internStatus' = InSelection or i.internStatus' = InPublishing)
        or
        i.internStatus = Completed and (i.internStatus' = InSelection or i.internStatus' = InProgress or i.internStatus' = InPublishing)
    )
}

// Fact to describe the possible status evolution of the application
fact allowedAppEvol {
    always (no a: Application | 
        a.AppStatus = SubmissionWaiting and (a.AppStatus' = AcceptedOffer or a.AppStatus' = RejectedOffer or a.AppStatus' = AcceptedToInternship)
        or
        a.AppStatus = SelectedToInterview and (a.AppStatus' = AcceptedOffer or a.AppStatus' = RejectedOffer or a.AppStatus' = SubmissionWaiting)
        or
        a.AppStatus = AcceptedToInternship and (a.AppStatus' = Rejected or a.AppStatus' = SelectedToInterview or a.AppStatus' = SubmissionWaiting)
        or
        a.AppStatus = AcceptedOffer and (a.AppStatus' = Rejected or a.AppStatus' = RejectedOffer or a.AppStatus' = AcceptedToInternship or a.AppStatus' = SelectedToInterview or a.AppStatus' = SubmissionWaiting)
        or
        a.AppStatus = RejectedOffer and (a.AppStatus' = Rejected or a.AppStatus' = AcceptedOffer or a.AppStatus' = AcceptedToInternship or a.AppStatus' = SelectedToInterview or a.AppStatus' = SubmissionWaiting)
        or
        a.AppStatus = Rejected and (a.AppStatus' = AcceptedOffer or a.AppStatus' = RejectedOffer or a.AppStatus' = AcceptedToInternship or a.AppStatus' = SelectedToInterview or a.AppStatus' = SubmissionWaiting)
    )
}



// An internship in publishing or selection cannot have students participating in it and feedbacks submitted
fact NoStudentsOrFeedbacksInInternshipInPublishingOrSelection{
    always all i: Internship | (i.internStatus = InPublishing or i.internStatus = InSelection) implies
    (no s: Student | i in s.participates) and (no f: Feedback | f in i.submittedFeedbacks)
}

// When internship is in publishing status, no applications submitted should have an interview scheduled
fact noInterviewsWhileInternshipInPublishing {
    always all i: Internship | i.internStatus = InPublishing implies (no a: i.submissions | a.interview != none)
}

// An application can be submitted to the internship only if the internship is in publishing status
fact SubmissionsMutableOnlyInPublishing {
    always all i: Internship | (i.internStatus != InPublishing or i.internStatus' != InPublishing) implies (i.submissions' = i.submissions)
}



// An internship can be in selection status only if at least one application has been submitted
fact InternshipInSelectionOnlyIfApplicationSubmitted{
    always all i: Internship | i.internStatus = InSelection implies (some a: Application | a in i.submissions)
}

// All applications of an internship in selection move from state SelectedToInterview to AcceptedToInternship (or Rejected) at the same step
fact NoSimultaneousSelectedAndAccepted {
    always all i: Internship | (i.internStatus = InSelection and some a: i.submissions | a.AppStatus = AcceptedToInternship) implies (all a: i.submissions | a.AppStatus = AcceptedToInternship or a.AppStatus = Rejected)
}



// If a student participates to an internship, then that internship is in progress or completed
fact NoStudentParticipatesInInternshipIfNotInProgressOrCompleted{
    always all s: Student, i: Internship | i in s.participates implies (i.internStatus = InProgress or i.internStatus = Completed)
}

// An internship can be in progress or completed only if at least one student participates in it
fact InternshipInProgressOrCompletedOnlyIfStudentParticipates{
    always all i: Internship | (i.internStatus = InProgress or i.internStatus = Completed) implies (some s: Student | i in s.participates)
}

// When an internship is in progress status or completed status, all applications should be in the final status: accepted offer, rejected offer or rejected
fact InternshipInProgressOrCompletedApplicationsInFinalStatus{
    always all i: Internship | (i.internStatus = InProgress or i.internStatus = Completed) implies
    (all a: i.submissions | (a.AppStatus = AcceptedOffer or a.AppStatus = RejectedOffer or a.AppStatus = Rejected))
}

// Every Student can only do one internship at a time
fact StudentCanDoOneInternshipsAtATime{
    always all s: Student | let concurrentParticipations = #(s.participates & {i: s.participates | i.internStatus = InProgress}) |
    concurrentParticipations <= 1
}

// Student application number should be more or equals to the number of internships they participated in
fact StudentApplicationsMoreThanParticipations{
    always all s: Student | #s.submits >= #s.participates 
}

// Student should have the offer accepted equal or less than the number of applications submitted and equal to the number of participations
fact StudentOffersAccepted{
    always all s: Student | 
    let numOffersAccepted = #(s.submits & {a: s.submits | a.AppStatus = AcceptedOffer}) |
    let numApplications = #s.submits |
    let numParticipations = #s.participates |
    numOffersAccepted <= numApplications and numOffersAccepted = numParticipations
}

// Student has participated if and only if he accepted the application related to the internship
fact StudentParticipatesInInternship{
    always all s: Student, i: Internship | i in s.participates implies
    (some a: Application | a in s.submits and a in i.submissions and a.AppStatus = AcceptedOffer)
}

// When an internship is in progress or completed, no more interviews should be scheduled
fact noChangeInInterviewsWhenInternshipInProgressOrCompleted{
    always all i: Internship | (i.internStatus = InProgress or i.internStatus = Completed) implies
    i.submissions.interview' = i.submissions.interview
}



// Once Internship is completed, no more feedbacks can be submitted
fact InternshipCompletedNoMoreFeedbacks{
    always all i: Internship | i.internStatus' = Completed implies (i.submittedFeedbacks' = i.submittedFeedbacks)
}

// Once Internship is in progress, feedbacks can be submitted
fact InProgressForFeedbacks{
    always all i: Internship | (#i.submittedFeedbacks' > #i.submittedFeedbacks) implies i.internStatus = InProgress
}

// Once Internship is completed, there should be at least 2 feedbacks
fact AtLeast2FeedbackIfCompleted{
    always all i: Internship | i.internStatus' = Completed implies (#i.submittedFeedbacks > 1)
}

// ---------------------------------------------------------------------------------------------------------------------------------
// ----------------------------------- Initialization ------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------------------------------------------------
// Forcing the initial state of the system
fact init {
    #University = 1
    #Company = 1
    #Student = 4
    #Internship = 1

    all i: Internship | i.internStatus = InPublishing
}

// ---------------------------------------------------------------------------------------------------------------------------------
// ------------------------------------ Assertions ---------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------------------------------------------------

// Assert that in every step of the system, the relationship between signatures holds
assert noOrphansOrMultipleCardinality {
    always all s: Student | one u: University | s in u.enrolls
    always all a: Application | one s: Student | a in s.submits
    always all a: Application | one i: Internship | a in i.submissions
    always all i: Internship | one c: Company | i in c.publishes
    always all f: Feedback | one i: Internship | f in i.submittedFeedbacks
    always all i: Interview | one a: Application | i in a.interview
    always all disj s1, s2: Student | no a: Application | (a in s1.submits and  a in s2.submits)
    always all disj i1,i2: Internship | no a: Application | (a in i1.submissions and  a in i2.submissions)
    always all s: Student, i: Internship | no disj a1,a2: s.submits | (a1 in i.submissions and a2 in i.submissions)
    always all s: Student | all i: s.participates | some a: s.submits | a in i.submissions
    always all disj c1,c2: Company | no i: Internship | (i in c1.publishes and  i in c2.publishes)
    always all disj i1,i2: Internship | no f: Feedback | (f in i1.submittedFeedbacks and  f in i2.submittedFeedbacks)
    always all f: Feedback | some i: Internship | f in i.submittedFeedbacks
    always all disj a1,a2: Application | no intv: Interview | (intv in a1.interview and intv in a2.interview)
    always all intv: Interview | some a: Application | intv in a.interview
}
check  noOrphansOrMultipleCardinality

// Assert that all application are in a consistent status in every step
assert NonExistAppStatusOutOfRange{
    always all a: Application | a.AppStatus in ApplicationStatus
}
check NonExistAppStatusOutOfRange for 5

// Assert that all internships are in a consistent status in every step
assert NonExistInternStatusOutOfRange{
    always all i: Internship | i.internStatus in InternshipStatus
}
check NonExistInternStatusOutOfRange for 5

// Assert that if internship is in publishing status, no applications should have an interview scheduled
assert NoInterviewIfInternshipInPublishing{
    always all i: Internship | i.internStatus = InPublishing implies 
    (all a: i.submissions | a.interview = none)
}
check NoInterviewIfInternshipInPublishing for 5

// Assert that if internship is in selection status, all applications should be in the defined status
assert NoStatusSubmissionWaitingInSelectionPhase{
    all i: Internship | i.internStatus = InSelection implies
    all a: i.submissions | 
    a.AppStatus = SelectedToInterview or
    a.AppStatus = AcceptedToInternship or
    a.AppStatus = AcceptedOffer or
    a.AppStatus = Rejected or
    a.AppStatus = RejectedOffer
}
check NoStatusSubmissionWaitingInSelectionPhase for 5

// Assert that if internship is in progress status, all applications should be in the final statuses
assert NotAcceptNoFinalStatus{
    all i: Internship | i.internStatus = InProgress or i.internStatus = Completed 
    implies
     (no a: i.submissions | a.AppStatus = SubmissionWaiting or a.AppStatus = SelectedToInterview or a.AppStatus = AcceptedToInternship)
}
check NotAcceptNoFinalStatus for 5

// Assert that if internship is in Completed status, then no changes in the feedbacks set
assert NoFeedBacksAfterInternshipCompleted{
    always all i: Internship | i.internStatus = Completed implies no f: Feedback | f in
    i.submittedFeedbacks' and f not in i.submittedFeedbacks
}
check NoFeedBacksAfterInternshipCompleted

// Assert that if internship not in progress or completed, then no feedbacks are be submitted
assert BeforeInProgressNoFeedbacks{
    always all i: Internship | i.internStatus != InProgress and i.internStatus != Completed implies
    i.submittedFeedbacks = none
}
check BeforeInProgressNoFeedbacks for 5

//Assert that interview is scheduled only if the application is selected to interview
assert ifRejectedNoInterviewIfSelectedInterview {
    no a1,a2:Application, i1,i2: Internship | 
        (a1.AppStatus = Rejected and i1.internStatus = InSelection and a1 in i1.submissions and a1.interview != none) and
        (a2.AppStatus = SelectedToInterview and i2.internStatus = InSelection and a2 in i2.submissions and a2.interview = none)
}
check ifRejectedNoInterviewIfSelectedInterview for 5

// Assert that always if an application is selected to interview, then an interview is scheduled
assert ExistInterviewIfSelectedToInterview{
    always all a:Application | a.AppStatus = SelectedToInterview implies a.interview != none
}
check ExistInterviewIfSelectedToInterview for 5

// Assert that if an interview is scheduled, then it will never be removed
assert OnceInterviewCreatedCannotBeRemoved{
    always all a: Application | a.interview != none implies a.interview' = a.interview
}
check OnceInterviewCreatedCannotBeRemoved for 5

// Assert that always a student is participating in at most one internship in progress
assert StudentCanNotDoTwoInternshipsAtATime{
    always all s: Student | all i1,i2: s.participates | (i1.internStatus = InProgress and i2.internStatus = InProgress) implies i1 = i2
}
check StudentCanNotDoTwoInternshipsAtATime for 5

// Assert that the concurrent participations of a student are less than or equal than 1
assert StudentCanOnlyHaveOneInternshipInProgress{
    always all s: Student | # {i: Internship | i in s.participates and i.internStatus = InProgress} <= 1    
}
check StudentCanOnlyHaveOneInternshipInProgress for 5

// Assert that if a student is participating in an internship, then the application related to the internship is in AcceptedOffer
assert RejectedOfferStudentNotParticipates{
    always all s: Student | all i: Internship | i in s.participates implies
    (no a: Application | a in s.submits and a in i.submissions and a.AppStatus != AcceptedOffer)
}
check RejectedOfferStudentNotParticipates for 5

// ---------------------------------------------------------------------------------------------------------------------------------
// ------------------------------------ Predicates ---------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------------------------------------------------
// Predicates to model the creation of an internship
pred internshipCreation {
    eventually (#Internship = 2 and all i: Internship | i.internStatus = InPublishing and after always #Internship = 2) and 
	always (all a: Application, i: Internship | (a in i.submissions and a.AppStatus = SubmissionWaiting) implies before i.internStatus = InPublishing)
}

// Predicates to model the submission of an application
pred applicationSubmission {
    eventually (some a: Application, s: Student, i: Internship | a in s.submits and a in i.submissions and a.AppStatus = SubmissionWaiting) and eventually #Application > 2
}

// Predicates to model the rejection of an application
pred applicationRejection {
    eventually (some s: Student, i: Internship, a: Application  | a in s.submits and a in i.submissions and a.AppStatus = Rejected)
}

// Predicates to model the selection of an application
pred applicationSelection {
    eventually (some s: Student, i: Internship, a: Application  | a in s.submits and a in i.submissions and a.AppStatus = SelectedToInterview)
}

// Predicates to model the acceptance of an application
pred applicationAcceptance {
    eventually (some s: Student, i: Internship, a: Application  | a in s.submits and a in i.submissions and a.AppStatus = AcceptedToInternship)
}

// Predicates to model the acceptance of an internship
pred internshipAcceptance {
    eventually (some s: Student, i: Internship, a: Application  | a in s.submits and a in i.submissions and a.AppStatus = AcceptedOffer)
}

// Predicates to model the rejection of an internship
pred internshipRejection {
    eventually (some s: Student, i: Internship, a: Application  | a in s.submits and a in i.submissions and a.AppStatus = RejectedOffer)
}

// Predicates to model the submission of a feedback
pred feedbackSubmission {
    eventually (some f: Feedback, i: Internship | f in i.submittedFeedbacks)
}

// Predicates to model the completion of all internships
pred allInternshipCompleted {
    eventually (all i: Internship | i.internStatus = Completed)
}

// RUN THE SYSTEM
run { 
    internshipCreation;applicationSubmission;applicationRejection;applicationSelection;
    applicationAcceptance;internshipAcceptance;internshipRejection;feedbackSubmission;allInternshipCompleted 
} for 7