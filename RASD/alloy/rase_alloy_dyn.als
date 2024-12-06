//-------------------------------Dynamic model---------------------------------
//----------------------------------------------------------------------------------------
//---------------------------------- Signatures ------------------------------------------
//----------------------------------------------------------------------------------------

abstract sig User {}        // Abstract class for all users

sig Student extends User {                             // Student class to model students' submitted applications and participations in internships
    var submits: set Application,         // Applications submitted by student
    var participates: set Internship         // Internships student has participated in
}{
    one u: University | this in u.enrolls
}

sig Company extends User {                            // Company class to model companies' published internships
    var publishes: set Internship            // Internships published by company
}

sig University extends User {                         // University class to model universities' students
    var enrolls: set Student                        // Students enrolled in university
}

sig Internship {                                      // Internship class to model internships' applications and feedbacks
    var submissions: set Application,               // Applications submitted by students for internship
    var submittedFeedbacks: set Feedback,           //or call them "reviews"
    var internStatus: one InternshipStatus
}{
    one c: Company | this in c.publishes
}             

var sig Application {                                     // Application class to model applications' interviews
   var interview: lone Interview,
   var AppStatus: one ApplicationStatus               // Interview scheduled for application
}{
    one s: Student | this in s.submits
}

var sig Feedback {}{
    one i: Internship | this in i.submittedFeedbacks
}                                       // Feedback class to model feedbacks submitted by students who participated in internships and companies who published them

var sig Interview {}  {
    one a: Application | this in a.interview
}                                    // Interview class to model interviews scheduled for applications

/*
model the status of an application:
SubmissionWaiting: the application has been submitted by the student and is waiting for the response from the company
SelectedToInterview: the application has been selected by the company for an interview
AcceptedToInternship: the application has been accepted by the company
AcceptedOffer: the application has been accepted by the student when the company has sent the offer
RejectedOffer: the application has been rejected by the student when the company has sent the offer
Rejected: the application has been rejected by the company in different phases
*/
abstract sig ApplicationStatus{}
one sig 
SubmissionWaiting, 
SelectedToInterview,
AcceptedToInternship, 
AcceptedOffer, 
RejectedOffer, 
Rejected extends ApplicationStatus{}


/*model the  status of internship:
When an internship is in publishing status, the company published the internship
When an internship is in selection status, the company is selecting the students for the offers: selected students to interview,
accepted students to the internship, rejected students, etc
When an internship is in progress status, when the students has accepted the offer and the internship started
When an internship is completed, the internship is finished
*/
abstract sig InternshipStatus{}
one sig 
InPublishing, 
InSelection,
InProgress,
Completed extends InternshipStatus{}

//------------------------------------------------------------------------------------------------------------------------------------------
//-------------------------- Facts for the dynamic model ----------------------------------
//----------------------------------------------------------------------------------------

//Facts used before in Static model

// Fact to ensure that each application is submitted by only one student (no application can be submitted by multiple students)
fact oneStudentPerApplication{
    always all disj s1, s2: Student | no a: Application | (a in s1.submits and  a in s2.submits)
}

// Fact to ensure that all applications have been submitted by a student (no orphan applications)
fact allApplicationsInStudent{
    always all a: Application | some s: Student | a in s.submits
}

// Fact to ensure that a student cannot submit multiple applications for the same internship
fact noRepeatedApplicationsForSameInternship{
   always all s: Student, i: Internship | no disj a1,a2: s.submits | (a1 in i.submissions and a2 in i.submissions)
}

// Fact to ensure that all internships that a student has participated in have an application submitted by the student
fact allStudentInternshipsHaveApplication{
    always all s: Student | all i: s.participates | some a: s.submits | a in i.submissions
}

// Fact to ensure that each internship is published by only one company (no internship can be published by multiple companies)
fact oneCompanyPerInternship{
    always all disj c1,c2: Company | no i: Internship | (i in c1.publishes and  i in c2.publishes)
}

// Fact to ensure that all internships have been published by a company (no orphan internships)
fact allInternshipsInCompany{
     always all i: Internship | some c: Company | i in c.publishes
}

// Fact to ensure that each student is enrolled in only one university (no student can be enrolled in multiple universities)
fact oneUniPerStudent{
     always all disj u1,u2: University | no s: Student | (s in u1.enrolls and  s in u2.enrolls)
}

// Fact to ensure that all students are enrolled in a university (no orphan students)
fact allStudentsInUni{
    always all s: Student | some u: University | s in u.enrolls
}

// Fact to ensure that each application is submitted for only one internship (no application can be submitted for multiple internships)
fact oneInternshipPerApplication{
     always all disj i1,i2: Internship | no a: Application | (a in i1.submissions and  a in i2.submissions)
}

// Fact to ensure that all applications have been submitted for an internship (no orphan applications)
fact allSelectedStudentsApplicationsInInternship{
     always all a: Application | some i: Internship | a in i.submissions
}

// Fact to ensure that each feedback is submitted for only one internship (no feedback can be submitted for multiple internships)
fact oneInternshipPerFeedback{
     always all disj i1,i2: Internship | no f: Feedback | (f in i1.submittedFeedbacks and  f in i2.submittedFeedbacks)
}

// Fact to ensure that all feedbacks have been submitted for an internship (no orphan feedbacks)
fact allFeedbacksInInternship{
     always all f: Feedback | some i: Internship | f in i.submittedFeedbacks
}

// Fact to ensure that each interview is scheduled for only one application (no interview can be scheduled for multiple applications)
fact oneApplicationPerInterview{
    always all disj a1,a2: Application | no intv: Interview | (intv in a1.interview and intv in a2.interview)
}

// Fact to ensure that all interviews have been scheduled for an application (no orphan interviews)
fact allInterviewsInApplication{
     always all intv: Interview | some a: Application | intv in a.interview
}

// Fact to ensure that a feedback is submitted only if at least a student has participated in the internship
fact feedbackOnlyIfStudentInInternship{
     always all f: Feedback, i: Internship | f in i.submittedFeedbacks 
     implies (some s: Student | i in s.participates and 
        (some a: Application | a in s.submits and a in i.submissions))
}

// Fact to ensure that all internships where a student has participated have an interview scheduled for the application
fact allStudentInternshipsHaveInterviewInApplication{
     always all s: Student, i: Internship | i in s.participates implies 
        (some a: Application | a in s.submits and a in i.submissions and
        (some intv: Interview | intv in a.interview))

}

//-----------------------------New Constraints------------------------------------

//-----------Application and Internship Statuses----------------
//Application can only have one status at a time (DONE with the Assert and Check)
fact ApplicationStatusCanOnlyHaveOnePhaseAtATime{
    always all a: Application | (one a.AppStatus and
    (a.AppStatus in SubmissionWaiting or 
    a.AppStatus in SelectedToInterview or 
    a.AppStatus in AcceptedToInternship or 
    a.AppStatus in AcceptedOffer or 
    a.AppStatus in Rejected or 
    a.AppStatus in RejectedOffer))
}

assert NonExistAppStatusOutOfRange{
    always all a: Application | a.AppStatus in ApplicationStatus
}
check NonExistAppStatusOutOfRange for 5

assert NoTwoAppStatusAtSameTime{
    always all a: Application | a.AppStatus in SubmissionWaiting implies
    a.AppStatus not in SelectedToInterview and 
    a.AppStatus not in AcceptedToInternship and 
    a.AppStatus not in AcceptedOffer and 
    a.AppStatus not in Rejected and 
    a.AppStatus not in RejectedOffer
}
check NoTwoAppStatusAtSameTime for 5

//Internship can only have one possible status at a time (DONE with the Assert and Check)
fact InternshipStatusCanOnlyHaveOnePhaseAtATime {
    always all i: Internship | one i.internStatus and 
    (i.internStatus in InPublishing or
    i.internStatus in InSelection or
    i.internStatus in InProgress or
    i.internStatus in Completed)
}

fact NoStudentParticipatesInInternshipIfNotInProgressOrCompleted{
    always all s: Student, i: Internship | i in s.participates implies
    (i.internStatus in InProgress or i.internStatus in Completed)
}

//When internship is in publishing status, no applications submitted should have an interview scheduled (DONE with the Assert and Check)
fact InternshipInPublishingNoneInterviews {
    always all i: Internship | i.internStatus = InPublishing implies (no a: i.submissions | a.interview != none)
}

assert NoInterviewInPublishing{
    always all i: Internship | i.internStatus = InPublishing implies 
    (all a: i.submissions | a.interview = none)
}
check NoInterviewInPublishing for 5

//When an internship is in selection status, all applications should be updated from submission waiting (DONE with the Assert and Check) 
fact InternshipInInterviewStatusAndItsApplications{
    always all i: Internship | i.internStatus in InSelection implies 
        (no a: i.submissions | a.AppStatus in SubmissionWaiting)        
}

assert NoStatusSubmissionWaitingInSelectionPhase{
    all i: Internship | i.internStatus in InSelection implies
    all a: i.submissions | 
    a.AppStatus in SelectedToInterview or
    a.AppStatus in AcceptedToInternship or
    a.AppStatus in AcceptedOffer or
    a.AppStatus in Rejected or
    a.AppStatus in RejectedOffer
}
check NoStatusSubmissionWaitingInSelectionPhase for 5

/*
When an internship is in progress status or completed status, all applications should be in the final status: accepted offer, rejected offer or rejected
(DONE with the Assert and Check) 
*/
fact InternshipInProgressOrCompletedApplicationsInFinalStatus{
    always all i: Internship | (i.internStatus = InProgress or i.internStatus = Completed) implies
    (all a: i.submissions | (a.AppStatus = AcceptedOffer or a.AppStatus = RejectedOffer or a.AppStatus = Rejected))
}

assert NotAcceptNoFinalStatus{
    all i: Internship | i.internStatus = InProgress or i.internStatus = Completed 
    implies
     (no a: i.submissions | a.AppStatus = SubmissionWaiting or a.AppStatus = SelectedToInterview or a.AppStatus = AcceptedToInternship)
}
check NotAcceptNoFinalStatus for 5

//Once Internship is completed, no more feedbacks can be submitted (DONE with the Assert and Check) 
fact InternshipCompletedNoMoreFeedbacks{
    always all i: Internship | i.internStatus = Completed implies
    (i.submittedFeedbacks' = i.submittedFeedbacks)
}

assert NoFeedBacksAfterInternshipCompleted{
    always all i: Internship | i.internStatus in Completed implies no f: Feedback | f in
    i.submittedFeedbacks' and f not in i.submittedFeedbacks
}
check NoFeedBacksAfterInternshipCompleted

//Before an internship enter in InProgress status, the feedbacks submitted should be equals to zero (DONE with the Assert and Check) 
fact NoFeedbacksBeforeInProgress{
    always all i: Internship | (i.internStatus = InPublishing or i.internStatus = InSelection )implies i.submittedFeedbacks=none
}

assert BeforeInProgressNoFeedbacks{
    always all i: Internship | i.internStatus not in InProgress and i.internStatus not in Completed implies
    i.submittedFeedbacks = none
}
check BeforeInProgressNoFeedbacks for 5

/*
If an internship is in publishing status, the next status should be InSelection if exists applications in the internship has been selected to interview otherwise remains in publishing status
If an internship is in selection status, the next status should be InProgress if exists applications in the internship has been accepted to the internship otherwise remains in selection status
If an internship is in progress status, the next status should be Completed
If an internship is in completed status, the next status should be Completed
*/

fact InternshipStatusTransitionAndItsApplications {
    always all i: Internship | 
        (i.internStatus = InPublishing implies (all a: i.submissions | a.AppStatus in SubmissionWaiting ))and 
        (i.internStatus = InSelection implies (all a: i.submissions | a.AppStatus = SelectedToInterview or a.AppStatus = Rejected or a.AppStatus = AcceptedToInternship)) and
        (i.internStatus = InProgress implies (all a: i.submissions | a.AppStatus = AcceptedOffer or a.AppStatus = Rejected or a.AppStatus = RejectedOffer) and (some a: i.submissions | a.AppStatus = AcceptedOffer)) and 
        (i.internStatus = Completed implies  (all a: i.submissions | a.AppStatus = AcceptedOffer or a.AppStatus = Rejected or a.AppStatus = RejectedOffer) and (some a: i.submissions | a.AppStatus = AcceptedOffer))
}

assert InProgressMustHaveOneAcceptedOffer{
    always all i: Internship | (i.internStatus = InProgress or i.internStatus = Completed )implies(
    (some a: i.submissions | a.AppStatus = AcceptedOffer) and (no a: i.submissions | a.AppStatus = SubmissionWaiting or a.AppStatus = SelectedToInterview or a.AppStatus = AcceptedToInternship)) 
}
check InProgressMustHaveOneAcceptedOffer for 5

fact InternshipStatusTransition{
    always all i: Internship | 
        (i.internStatus = InPublishing implies 
            i.internStatus' = InSelection and
                i.internStatus'' = InProgress and
                    i.internStatus''' = Completed) and
        (i.internStatus = InSelection implies
                i.internStatus'= InProgress and
                    i.internStatus'' = Completed) and
        (i.internStatus = InProgress implies
            i.internStatus' = Completed)
            and
        (i.internStatus = Completed implies
            i.internStatus' = Completed)
    
}

fact ApplicationTransition{
    always all a: Application |
    (a.AppStatus= SubmissionWaiting implies (a.AppStatus' = SelectedToInterview or a.AppStatus'=Rejected)) and 
    (a.AppStatus= SelectedToInterview implies (a.AppStatus' = AcceptedToInternship or a.AppStatus' = Rejected)) and
    (a.AppStatus= AcceptedToInternship implies (a.AppStatus' = AcceptedOffer or a.AppStatus' = RejectedOffer)) and
    (a.AppStatus= AcceptedOffer implies a.AppStatus' = AcceptedOffer) and
    (a.AppStatus= RejectedOffer implies a.AppStatus' = RejectedOffer) and
    (a.AppStatus= Rejected implies a.AppStatus' = Rejected)
}


assert NoApplicationTransitionOutOrder{
    always all a: Application | a.AppStatus in AcceptedOffer implies
         a.AppStatus' in AcceptedOffer
}
check NoApplicationTransitionOutOrder for 5

assert NoInternshipOutOrder{
    always all i: Internship | i.internStatus in Completed implies
         i.internStatus' = Completed 
}
check NoInternshipOutOrder for 5

assert NoOrderInternOutRule{
    always all i: Internship | i.internStatus in InPublishing implies(
    i.internStatus' = InSelection and 
        (i.internStatus'' = InProgress and(
            i.internStatus''' = Completed)))
}
check NoOrderInternOutRule for 5

assert NoOrderAppOutRule{
    always all a: Application | a.AppStatus in SubmissionWaiting implies (
    (a.AppStatus' = SelectedToInterview and 
        a.AppStatus'' = Rejected and 
            a.AppStatus''' = Rejected) or
    (a.AppStatus' = Rejected and 
        a.AppStatus'' = Rejected) or
    (a.AppStatus' = SelectedToInterview and 
        a.AppStatus'' = AcceptedToInternship and 
            a.AppStatus''' = AcceptedOffer and
                a.AppStatus'''' = AcceptedOffer) or
    (a.AppStatus' = SelectedToInterview and
        a.AppStatus'' = AcceptedToInternship and
            a.AppStatus''' = RejectedOffer and 
                a.AppStatus'''' = RejectedOffer) 
    )
}
check NoOrderAppOutRule for 5

//Variation of Interview in every state of the application
fact InterviewInEveryStateOfApplication{
    always all a: Application | 
    (a.AppStatus = SubmissionWaiting implies a.interview = none) and
    (a.AppStatus = SelectedToInterview implies a.interview != none) and
    (a.AppStatus = AcceptedToInternship implies a.interview != none) and
    (a.AppStatus = AcceptedOffer implies a.interview != none) and
    (a.AppStatus = RejectedOffer implies a.interview != none)
}

//Number of invitations sent by a company should be equal to the number of interviews scheduled and less or equal to the number of applications submitted
fact NumInvitationsEqualsNumInterviews{
    always all i: Internship | i.internStatus = InSelection implies
    (all a: i.submissions | a.AppStatus = SelectedToInterview implies a.interview != none)
}

fact InInterviewCanNotBeRemoved{
    always all a: Application | a.interview!=none implies (a.interview'=a.interview)
}

assert ExistInterviewIfSelectedToInterview{
    always all a:Application | a.AppStatus = SelectedToInterview implies
    a.interview != none
}
check ExistInterviewIfSelectedToInterview for 5

assert OnceInterviewCreatedCannotBeRemoved{
    always all a: Application | a.interview != none implies
    a.interview' = a.interview
}
check OnceInterviewCreatedCannotBeRemoved for 5


fact BeforeInSelectionNoInterviews{
    always all i: Internship | i.internStatus = InPublishing implies
    (no a: i.submissions | a.interview != none)
}

fact AfterInSelectionInterviewsInvariant{
    always all i: Internship | (i.internStatus = InProgress or i.internStatus = Completed )implies
    i.submissions.interview' = i.submissions.interview
}

//Every Student can only do one internship at a time (DONE with the Assert and Check)
fact StudentParticipatesInternship{
    always all s: Student | all disj i: s.participates | (i.internStatus = InProgress or i.internStatus = Completed) 
}

fact StudentCanDoOneInternshipsAtATime{
    always all s: Student | # {i: Internship | i in s.participates and i.internStatus = InProgress} <= 1
}

assert StudentCanNotDoTwoInternshipsAtATime{
    always all s: Student | all i1,i2: s.participates | (i1.internStatus = InProgress and i2.internStatus = InProgress) implies
    i1 = i2
}
check StudentCanNotDoTwoInternshipsAtATime for 5

assert StudentCanOnlyHaveOneInternshipInProgress{
    always all s: Student | # {i: Internship | i in s.participates and i.internStatus = InProgress} <= 1    
}
check StudentCanOnlyHaveOneInternshipInProgress for 5

//Student application number should be more or equals to the number of internships he/she has participated in
fact StudentApplicationsInInternships{
    always all s: Student | #s.submits >= #s.participates 
}

//Student should have the offer accepted equal or less than the number of applications submitted
fact StudentOffersAccepted{
    always all s: Student | 
    let numOffersAccepted = #(s.submits & {a: s.submits | a.AppStatus = AcceptedOffer}) |
    let numApplications = #s.submits |
    numOffersAccepted <= numApplications
}

//Student has the internship participated if and only if he accepted the application related to the internship
fact StudentParticipatesInInternship{
    always all s: Student, i: Internship | i in s.participates implies
    (some a: Application | a in s.submits and a in i.submissions and a.AppStatus = AcceptedOffer )
}
assert RejectedOfferStudentNotParticipates{
    always all s: Student | all i: Internship | i in s.participates implies
    (no a: Application | a in s.submits and a in i.submissions and a.AppStatus not in AcceptedOffer)
}
check RejectedOfferStudentNotParticipates for 5

fact InSelectionStudentApplication{
    always all s: Student, a: Application| a in s.submits implies 
    after a in s.submits
}

fact SubmissionsMutableOnlyInPublishing {
    always all i: Internship |
        i.internStatus not in InPublishing implies
        (i.submissions' = i.submissions)
}

fact FeedbackExistCanBeCancelled{
    always all f: Feedback, i: Internship | f in i.submittedFeedbacks implies
    after f in i.submittedFeedbacks
}
//Feedback in Completed status means feedback has been submitted in the In Progress status
fact FeedbackInCompletedStatus{
    always all f: Feedback, i: Internship | f in i.submittedFeedbacks and i.internStatus = Completed implies
    historically f in i.submittedFeedbacks
}

// ---------Basic run commands to show the model----------------
run { some s: Student, i: Internship | i in s.participates} for 10

run { some i: Internship |  i.internStatus in InPublishing} for 9
run { some  i: Internship | i.internStatus in InSelection} for 5

run { some s: Student, i: Internship | i in s.participates and i.internStatus in InProgress} for 5

run { some s: Student, i: Internship | i in s.participates and i.internStatus in Completed} for 5

run { some s: Student, a: Application | a in s.submits and a.AppStatus in AcceptedOffer} for 5

run { some s: Student, a: Application | a in s.submits and a.AppStatus in RejectedOffer} for 5

run { some s: Student, a: Application | a in s.submits and a.AppStatus in Rejected} for 5

run { some s: Student, a: Application | a in s.submits and a.AppStatus in SubmissionWaiting} for 5

run { some s: Student, a: Application | a in s.submits and a.AppStatus in SelectedToInterview} for 5

run { some s: Student, a: Application | a in s.submits and a.AppStatus in AcceptedToInternship} for 5


