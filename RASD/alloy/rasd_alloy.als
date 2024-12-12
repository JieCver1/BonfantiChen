//----------------------------------------------------------------------------------------------------------------------------------
//---------------------------- RASD Alloy Static Model -----------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------
//---------------------------------- Signatures ------------------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------

abstract sig User {}                 // Abstract signature for all users

sig Student extends User {           // Student signature to model students' submitted applications and participations in internships
    submits: set Application,        // Applications submitted by student
    participates: set Internship     // Internships student has participated in
}

sig Company extends User {           // Company signature to model companies' published internships
    publishes: set Internship        // Internships published by company
}

sig University extends User {        // University signature to model universities' students
    enrolls: set Student             // Students enrolled in university
}

sig Internship {                     // Internship signature to model internships' applications and feedbacks
    submissions: set Application,    // Applications submitted by students for internship
    submittedFeedbacks: set Feedback // Feedbacks submitted by student who participated in internship
}               

sig Application {                    // Application signature to model applications' interviews
    interview: lone Interview        // Interview scheduled for application
}

sig Feedback {}  // Feedback signature to model feedbacks submitted by students who participated in internships and companies who published them

sig Interview {} // Interview signature to model interviews scheduled for applications

//----------------------------------------------------------------------------------------------------------------------------------
//-------------------------- Facts for the static model ----------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------
// Fact to ensure that each application is submitted by only one student (no application can be submitted by multiple students)
fact oneStudentPerApplication{
    all s1,s2: Student | no a: Application | (a in s1.submits and  a in s2.submits and s1 != s2)
}

// Fact to ensure that all applications have been submitted by a student (no orphan applications)
fact allApplicationsInStudent{
    all a: Application | some s: Student | a in s.submits
}

// Fact to ensure that a student cannot submit multiple applications for the same internship
fact noRepeatedApplicationsForSameInternship{
    all s: Student | no i: Internship | 
        (some a1,a2: s.submits | (a1 in i.submissions and a2 in i.submissions and a1 != a2))
}

// Fact to ensure that all internships that a student has participated in have an application submitted by the student
fact allStudentInternshipsHaveApplication{
    all s: Student, i: s.participates | some a: s.submits | a in i.submissions
}

// Fact to ensure that each internship is published by only one company (no internship can be published by multiple companies)
fact oneCompanyPerInternship{
    all c1,c2: Company | no i: Internship | (i in c1.publishes and  i in c2.publishes and c1 != c2)
}

// Fact to ensure that all internships have been published by a company (no orphan internships)
fact allInternshipsInCompany{
    all i: Internship | some c: Company | i in c.publishes
}

// Fact to ensure that each student is enrolled in only one university (no student can be enrolled in multiple universities)
fact oneUniPerStudent{
    all u1,u2: University | no s: Student | (s in u1.enrolls and  s in u2.enrolls and u1 != u2)
}

// Fact to ensure that all students are enrolled in a university (no orphan students)
fact allStudentsInUni{
    all s: Student | some u: University | s in u.enrolls
}

// Fact to ensure that each application is submitted for only one internship (no application can be submitted for multiple internships)
fact oneInternshipPerApplication{
    all i1,i2: Internship | no a: Application | (a in i1.submissions and  a in i2.submissions and i1 != i2)
}

// Fact to ensure that all applications have been submitted for an internship (no orphan applications)
fact allSelectedStudentsApplicationsInInternship{
    all a: Application | some i: Internship | a in i.submissions
}

// Fact to ensure that each feedback is submitted for only one internship (no feedback can be submitted for multiple internships)
fact oneInternshipPerFeedback{
    all i1,i2: Internship | no f: Feedback | (f in i1.submittedFeedbacks and  f in i2.submittedFeedbacks and i1 != i2)
}

// Fact to ensure that all feedbacks have been submitted for an internship (no orphan feedbacks)
fact allFeedbacksInInternship{
    all f: Feedback | some i: Internship | f in i.submittedFeedbacks
}

// Fact to ensure that each interview is scheduled for only one application (no interview can be scheduled for multiple applications)
fact oneApplicationPerInterview{
    all a1,a2: Application | no intv: Interview | (intv in a1.interview and intv in a2.interview and a1 != a2)
}

// Fact to ensure that all interviews have been scheduled for an application (no orphan interviews)
fact allInterviewsInApplication{
    all intv: Interview | some a: Application | intv in a.interview
}

// Fact to ensure that a feedback is submitted only if at least a student has participated in the internship
fact feedbackOnlyIfStudentInInternship{
    all f: Feedback, i: Internship | f in i.submittedFeedbacks implies (some s: Student | i in s.participates and 
        (some a: Application | a in s.submits and a in i.submissions))
}

// Fact to ensure that all internships where a student has participated have an interview scheduled for the application
fact allStudentInternshipsHaveInterviewInApplication{
    all s: Student, i: Internship | i in s.participates implies 
        (some a: Application | a in s.submits and a in i.submissions and 
        (some intv: Interview | intv in a.interview))
}

//----------------------------------------------------------------------------------------------------------------------------------
//----------------------- Predicates to show the static model ----------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------------------------
// Example 0: Simple model with 1 university, 2 students, 2 internships, and 1 company.
// Only 1 student participates in an internship (the other one does not), both students submit different number of applications, 
// no bounds on the number of interviews and feedbacks.
pred example0 {
    #University = 1
    #Student = 2
    #Internship = 2
    #Company = 1

    one s: Student | #s.submits = 1
    one s: Student | #s.submits = 2
    one s: Student | #s.participates = 1
    one s: Student | #s.participates = 0
} 
run example0 for 4

// Example 1: More structured model with 2 universities, 5 students, 3 internships, and 2 companies.
// All students submit more than 1 application, all students participate in less internships than the number of applications they submitted,
// at least 1 student participates in an internship, applications and feedbacks are more than 0, and the number of interviews is less than the 
// number of applications.
pred example1 {
    #University = 2
    #Student = 5
    #Internship = 3
    #Company = 2

    some s: Student | #s.submits > 1
    all s: Student | #s.participates < #s.submits
    some s: Student | #s.participates > 0

    #Application > 0
    #Feedback > 0
    #Interview < #Application
} 
run example1 for 9

// Example 2: More complex model with 2 universities, 5 students, 5 internships, and 2 companies.
// All universities have less than 3 students enrolled, at least 1 student submits more than 1 application, 
// at least 1 student participates in an internship, at least 1 internship has no submissions,
// all internships have less than 3 submitted feedbacks, and the number of submissions is greater than the 
// number of students participating. Each company has less than 3 internships published (so that both companies
// have at least 1 internship published).
pred example2 {
    #University = 2
    #Student = 5
    #Internship = 5
    #Company = 2
    
    #Application > 0
    #Feedback > 0
    #Interview < #Application

    all u: University | #u.enrolls <= 3
    all u: University | (some s: Student | s in u.enrolls and #s.submits > 0 and #s.participates > 0)

    some s: Student | #s.submits > 1
    all s: Student | #s.submits < 3

    some s: Student | #s.participates > 0
    some s: Student | #s.participates > 1

    some i: Internship | #i.submissions = 0
    all i: Internship | #i.submittedFeedbacks < 3

    all c: Company | #c.publishes <= 3
}
run example2 for 13