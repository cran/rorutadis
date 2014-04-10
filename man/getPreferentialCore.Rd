\name{getPreferentialCore}
\alias{getPreferentialCore}
\title{Identify preferential core}
\usage{
getPreferentialCore(preferentialReducts)
}
\arguments{
  \item{preferentialReducts}{List of all preferential
  reducts (a result of \code{\link{explainAssignment}}).}
}
\value{
Preferential core as a vector of restriction indices. To
find out about restrictions by their indices use
\code{\link{getRestrictions}}.
}
\description{
This function identifies preferential core.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.5), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

possibleAssignments <- calculateAssignments(problem, FALSE)
alternative <- 4
assignment <- c(min(which(possibleAssignments[alternative, ])),
               max(which(possibleAssignments[alternative, ])))

preferentialReducts <- explainAssignment(alternative,
   assignment, problem)
preferentialCore <- getPreferentialCore(preferentialReducts)
coreRestrictions <- getRestrictions(problem, preferentialCore)
}
\seealso{
\code{\link{explainAssignment}}
\code{\link{getRestrictions}}
}

