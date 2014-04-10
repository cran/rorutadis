\name{compareAssignments}
\alias{compareAssignments}
\title{Compare assignments}
\usage{
compareAssignments(problem, necessary = TRUE)
}
\arguments{
  \item{problem}{Problem for which assignments will be
  compared.}

  \item{necessary}{Whether necessary or possible
  assignments.}
}
\value{
\emph{n} x \emph{n} logical matrix, where \code{n} is a
number of alternatives. Cell \code{[i, j]} is \code{TRUE}
if \emph{a_i} is assigned to class at least as good as
class of \emph{a_j} for all compatible value functions for
necessary assignments or for at least one compatible value
function for possible assignments.
}
\description{
This function compares assignments. In this version of the
package only necessary assignments are supported.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

resultOfComparison <- compareAssignments(problem)
}

