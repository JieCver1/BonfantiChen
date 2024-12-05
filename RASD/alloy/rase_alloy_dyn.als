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

var sig Internship {                                      // Internship class to model internships' applications and feedbacks
    var submissions: set Application,               // Applications submitted by students for internship
    var submittedFeedbacks: set Feedback,           //or call them "reviews"
    var internStatus: one InternshipStatus
}{
    one s: Student | this in s.participates
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
     always all f: Feedback, i: Internship | f in i.submittedFeedbacks implies (some s: Student | i in s.participates and 
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
    always all a: Application | one a.AppStatus and
    (a.AppStatus in SubmissionWaiting or 
    a.AppStatus in SelectedToInterview or 
    a.AppStatus in AcceptedToInternship or 
    a.AppStatus in AcceptedOffer or 
    a.AppStatus in Rejected or 
    a.AppStatus in RejectedOffer)
}
/*
assert NonExistAppStatusOutOfRange{
    all a: Application | a.AppStatus in ApplicationStatus
}
check NonExistAppStatusOutOfRange for 5
assert NoTwoAppStatusAtSameTime{
    all a: Application | a.AppStatus in SubmissionWaiting implies 
    a.AppStatus not in SelectedToInterview and 
    a.AppStatus not in AcceptedToInternship and 
    a.AppStatus not in AcceptedOffer and 
    a.AppStatus not in Rejected and 
    a.AppStatus not in RejectedOffer
}
check NoTwoAppStatusAtSameTime for 5
*/

//Internship can only have one possible status at a time (DONE with the Assert and Check)
fact InternshipStatusCanOnlyHaveOnePhaseAtATime {
    always all i: Internship | one i.internStatus and 
    (i.internStatus in InPublishing or
    i.internStatus in InSelection or
    i.internStatus in InProgress or
    i.internStatus in Completed)
}

//When internship is in publishing status, no applications submitted should have an interview scheduled (DONE with the Assert and Check)
fact InternshipInPublishingNoneInterviews{
    always all i: Internship | i.internStatus = InPublishing implies
    all a: i.submissions | a.interview = none
}
/*
assert NoInterviewInPublishing{
    all i: Internship | i.internStatus = InPublishing implies
    no a: i.submissions | a.interview != none
}
check NoInterviewInPublishing for 5
*/

//When an internship is in selection status, all applications should be updated from submission waiting (DONE with the Assert and Check) 
fact InternshipInInterviewStatusAndItsApplications{
    always all i: Internship | i.internStatus in InSelection implies (
        no a: i.submissions | a.AppStatus in SubmissionWaiting)        
}
/*
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
*/

/*
When an internship is in progress status or completed status, all applications should be in the final status: accepted offer, rejected offer or rejected
(DONE with the Assert and Check) 
*/
fact InternshipInProgressOrCompletedApplicationsInFinalStatus{
    always all i: Internship | i.internStatus = InProgress or i.internStatus = Completed implies
    (all a: i.submissions | (a.AppStatus = AcceptedOffer or a.AppStatus = RejectedOffer or a.AppStatus = Rejected)
    )
}
/*
assert NotAcceptNoFinalStatus{
    all i: Internship | i.internStatus = InProgress or i.internStatus = Completed 
    implies
     (no a: i.submissions | a.AppStatus = SubmissionWaiting or a.AppStatus = SelectedToInterview or a.AppStatus = AcceptedToInternship)
}
check NotAcceptNoFinalStatus for 5
*/
//When an application is accepted by the student, such application should be accepted by the company before (DONE with the Assert and Check) 
fact AcceptedOfferOnceAcceptedToInternship{
    always all a: Application | a.AppStatus = AcceptedOffer implies
    before a.AppStatus = AcceptedToInternship
}
/*
assert NoApplicationCanBeAcceptedIfNotAcceptedByCompany{
    all a: Application | a.AppStatus = AcceptedOffer implies
    historically a.AppStatus = AcceptedToInternship
}
check NoApplicationCanBeAcceptedIfNotAcceptedByCompany for 5
*/

//Once Internship is completed, no more feedbacks can be submitted (DONE with the Assert and Check) 
fact InternshipCompletedNoMoreFeedbacks{
    always all i: Internship | i.internStatus = Completed implies
    always i.submittedFeedbacks' = i.submittedFeedbacks
}
/*
assert NoFeedBacksAfterInternshipCompleted{
    always all i: Internship | i.internStatus in Completed implies no f: Feedback | f in
    i.submittedFeedbacks' and f not in i.submittedFeedbacks
}
check NoFeedBacksAfterInternshipCompleted
*/

//Before an internship enter in InProgress status, the feedbacks submitted should be equals to zero (DONE with the Assert and Check) 
fact NoFeedbacksBeforeInProgress{
    always all i: Internship | i.internStatus = InPublishing or i.internStatus = InSelection implies i.submittedFeedbacks=none
}
/*
assert BeforeInProgressNoFeedbacks{
    always all i: Internship | i.internStatus not in InProgress and i.internStatus not in Completed implies
    i.submittedFeedbacks = none
}
check BeforeInProgressNoFeedbacks for 5
*/

//Transaction rule:
pred validInternshipStatusTransition(i: InternshipStatus) {
    //pre condition -> post condition
    (i= InPublishing implies i' = InSelection ) and 
    (i= InSelection implies i' = InProgress) and
    (i= InProgress implies i' = Completed) and
    (i= Completed implies i' = Completed)
    //invariant of internship 
    Internship' = Internship
    
}

pred validApplicationStatusTransition(a: ApplicationStatus){ 
    (a= SubmissionWaiting implies a' = SelectedToInterview or a'=Rejected) and 
    (a= SelectedToInterview implies a' = AcceptedToInternship or a' = Rejected) and
    (a= AcceptedToInternship implies a' = AcceptedOffer or a' = RejectedOffer) and
    (a= AcceptedOffer implies a' = AcceptedOffer) and
    (a= RejectedOffer implies a' = RejectedOffer) and
    (a= Rejected implies a' = Rejected)
    //invariant of application
    Application' = Application
}
//(DONE with the Assert and Check)
//Internship status should be changed in order: InPublishing -> InInterview -> FinalOffer -> InProgress -> Completed
fact InternshipStatusOrder{
    always all i: Internship | validInternshipStatusTransition[i.internStatus]
}
//(DONE with the Assert and Check)
//Application status should be changed in order: SubmissionWaiting -> SelectedToInterview -> AcceptedToInternship -> AcceptedOffer if everything goes well
//Otherwise, it will be Rejected or RejectedOffer
fact ApplicationStatusOrder{
    always all a: Application | validApplicationStatusTransition[a.AppStatus]
}
/*
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
    always all i: Internship | i.internStatus in InPublishing implies
    after i.internStatus = InSelection and 
        after i.internStatus = InProgress and
            after i.internStatus = Completed
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
*/
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
    all a: i.submissions | a.AppStatus = SelectedToInterview implies
    a.interview != none
}

fact InInterviewCanNotBeRemoved{
    always all a: Application | a.interview!=none implies
    always a.interview'=a.interview and a.AppStatus'!=none
}
/*
assert ExistInterviewIfSelectedToInterview{
    always all a:Application | a.AppStatus = SelectedToInterview implies
    a.interview != none
}
check ExistInterviewIfSelectedToInterview for 5

assert OnceInterviewCreatedCannotBeRemoved{
    always all a: Application | a.interview != none implies
    always a.interview' = a.interview
}
check OnceInterviewCreatedCannotBeRemoved for 5
*/

fact BeforeInSelectionNoInterviews{
    always all i: Internship | i.internStatus = InPublishing implies
    no a: i.submissions | a.interview != none
}

fact AfterInSelectionInterviewsInvariant{
    always all i: Internship | i.internStatus = InProgress or i.internStatus = Completed implies
    i.submissions.interview' = i.submissions.interview
}

//Every Student can only do one internship at a time (DONE with the Assert and Check)
fact StudentInOneInternshipAtATime{
    always all s: Student | no disj i1,i2: s.participates | (i1.internStatus = InProgress and i2.internStatus = InProgress)
}
/*
assert StudentCanNotDoTwoInternshipsAtATime{
    always all s: Student | all i1,i2: s.participates | (i1.internStatus = InProgress and i2.internStatus = InProgress) implies
    i1 = i2
}
check StudentCanNotDoTwoInternshipsAtATime for 5

assert StudentCanOnlyHaveOneInternshipInProgress{
    always all s: Student | # {i: Internship | i in s.participates and i.internStatus = InProgress} <= 1    
}
check StudentCanOnlyHaveOneInternshipInProgress for 5
*/

//Student application number should be equal to the number of internships he/she has participated in
fact StudentApplicationsInInternships{
    always all s: Student | 
    let numApplications = #s.submits | 
    let numInternships = #s.participates |
    numApplications = numInternships
}

//Student should have the offer accepted equal or less than the number of applications submitted
fact StudentOffersAccepted{
    always all s: Student | 
    let numOffersAccepted = #(s.submits & {a: s.submits | a.AppStatus = AcceptedOffer}) |
    let numApplications = #s.submits |
    numOffersAccepted <= numApplications
}
/*
------------------------TO DO------------------------
//---Dynamic scenarios---

//Student submits an application for an internship
pred SubmitApplicationForInternship(s: Student, i: Internship, a: Application) {
    always (all s: Student, i: Internship, a: Application |
    i in
    a.interview' = none and
    a.AppStatus' = SubmissionWaiting and
    Application' = Application + a and
    s.submits' = s.submits + a and
    i.submissions' = i.submissions + a)

}

pred CompanyPublishInternship {
    eventually all c: Company, i: Internship |
    i.internStatus = InPublishing and
    i not in c.publishes and
    c.publishes' = c.publishes + i
}

pred CompanyCreateInterview {
    eventually all i: Internship, a: Application, intv: Interview |
    a in i.submissions and
    a.AppStatus = SelectedToInterview and
    intv not in a.interview and
    Interview' = Interview + intv and
    a.interview = none and 
    a.interview' = intv
}

pred StudentRegisterToSystem {
    eventually all s: Student, u: University |
    s not in u.enrolls and
    u.enrolls' = u.enrolls + s
}

pred StudentRejectedFromInterview {
    eventually all s: Student, a: Application, intv: Interview|
    a in s.submits and
    a.AppStatus = SelectedToInterview and
    a.interview = intv and
    always a.AppStatus' = Rejected
}

pred CompanySendInterviewResult {
    eventually all i: Internship| some a: Application | 
    a in i.submissions and a.AppStatus = AcceptedToInternship implies
    i.internStatus' = WaitingStuDecision and 
    a.AppStatus' = Rejected or a.AppStatus' = AcceptedToInternship
}

pred StudentDecision {
    eventually all s: Student, a: Application |
    a in s.submits and a.AppStatus = AcceptedToInternship implies
    a.AppStatus' = AcceptedOffer or a.AppStatus' = RejectedOffer
}


pred startInternship {
    eventually all i: Internship | 
    i.internStatus = FinalOffer implies
    i.internStatus' = InProgress
}

pred SubmitFeedback{
    eventually all s: Student, i: Internship, f: Feedback |
    f not in i.submittedFeedbacks and
    i in s.participates and
    i.submittedFeedbacks' = i.submittedFeedbacks + f
    and i.internStatus = InProgress
}

pred CloseInternship{
    eventually all i: Internship | 
    i.internStatus = InProgress implies
    i.internStatus' = Completed
}

// Example 0: Simple model with 1 university, 2 students, 2 internships, and 1 company.
// Only 1 student participates in an internship (the other one does not), both students submit different number of applications, 
// no bounds on the number of interviews and feedbacks.
run StudentApplicationsLessThanInternships for 2 but exactly 1 Student, 2 Internship, 1 Company, 1 University, 2 Application, 1 Interview, 1 Feedback

run SubmitApplicationForInternship for 2
*/