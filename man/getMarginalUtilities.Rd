\name{getMarginalUtilities}
\alias{getMarginalUtilities}
\title{Get marginal utilities}
\usage{
getMarginalUtilities(problem, solution)
}
\arguments{
  \item{problem}{Problem whose model was solved.}

  \item{solution}{Result of model solving (e.g. result of
  \code{\link{findRepresentativeFunction}} or
  \code{\link{investigateUtility}}).}
}
\value{
A \emph{n} x \emph{m} matrix containing marginal values of
\code{n} alternatives on \code{m} criteria.
}
\description{
This function extracts alternatives marginal values from
model solution.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

representativeFunction <- findRepresentativeFunction(problem, 0)
marginalUtilities <- getMarginalUtilities(problem, representativeFunction)
}
\seealso{
\code{\link{findRepresentativeFunction}}
\code{\link{getAssignments}}
\code{\link{getCharacteristicPoints}}
\code{\link{getThresholds}}
\code{\link{investigateUtility}}
}

