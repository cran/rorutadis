\name{getAssignments}
\alias{getAssignments}
\title{Get assignments}
\usage{
getAssignments(problem, solution)
}
\arguments{
  \item{problem}{Problem whose model was solved.}

  \item{solution}{Result of model solving (e.g. result of
  \code{\link{findRepresentativeFunction}} or
  \code{\link{investigateUtility}}).}
}
\value{
Vector of alternative assignments. Each element contains an
index of a class that corresponding alternative was
assigned to.
}
\description{
This function returns assignments for given model solution.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

representativeFunction <- findRepresentativeFunction(problem, 0)
assignments <- getAssignments(problem, representativeFunction)
}
\seealso{
\code{\link{findRepresentativeFunction}}
\code{\link{getCharacteristicPoints}}
\code{\link{getMarginalUtilities}}
\code{\link{getThresholds}}
\code{\link{investigateUtility}}
}

