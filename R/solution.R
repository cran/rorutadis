#### SOLVING MODEL

#' @import Rglpk
extremizeVariable <- function(model, variableIndex, maximize) {
  obj <- rep(0, ncol(model$lhs))
  obj[variableIndex] <- 1  
  Rglpk_solve_LP(obj, model$lhs, model$dir, model$rhs, max = maximize,
                 types = model$types)
}

maximizeEpsilon <- function(model, epsilonIndex) {
  return (extremizeVariable(model, epsilonIndex, TRUE))
}

isModelConsistent <- function(model, epsilonIndex) {
  ret <- maximizeEpsilon(model, epsilonIndex)
  return (ret$status == 0 && ret$optimum >= RORUTADIS_MINEPS)
}


#### SOLUTION

#' Get thresholds
#'
#' This function extracts values of thresholds from model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return Vector containing \code{h-1} thresholds from \code{t_1} to \code{t_h-1}
#' where \code{t_p-1} is lower threshold of class \code{C_p} and \code{h} is
#' number of classes.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getAssignments}}
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getMarginalUtilities}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' thresholds <- getThresholds(problem, representativeFunction)
#' @export
getThresholds <- function(problem, solution) {
  firstThresholdIndex <- getFirstThresholdIndex(problem)
  lastThresholdIndex <- getLastThresholdIndex(problem)
  return (solution$solution[firstThresholdIndex:lastThresholdIndex])
}

#' Get marginal utilities
#'
#' This function extracts alternatives marginal values from model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return A \emph{n} x \emph{m} matrix containing marginal values of \code{n} alternatives
#' on \code{m} criteria.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getAssignments}}
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getThresholds}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' marginalUtilities <- getMarginalUtilities(problem, representativeFunction)
#' @export
getMarginalUtilities <- function(problem, solution) {
  levels <- getLevels(problem$perf)
  offsets <- getOffsets(levels)
  epsilonIndex <- getNrVars(levels)
  altVars <- buildAltVariableMatrix(problem$perf)
  
  utility <- matrix(ncol = ncol(problem$perf), nrow = nrow(problem$perf))
  
  for (i in seq_len(length(levels))) {    
    for (j in seq_len(length(levels[[i]]))) {
      index <- offsets[i] + j - 1
      for (k in seq_len(nrow(altVars))) {
        if (altVars[k, index] == 1) {
          utility[k, i] <- solution$solution[index]
        }
      }
    }
  }
  
  return (utility)
}

#' Get characteristic points
#'
#' This function extracts values of characteristic points from model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return List of \code{m} matrices for each of \code{m} criteria.
#' Each row \code{c(g, u)} of each matrix contains coordinates of a single
#' characteristic point, where \code{g} - evaluation on corresponding criterion,
#' \code{u} - marginal utility.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getAssignments}}
#' \code{\link{getMarginalUtilities}}
#' \code{\link{getThresholds}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' characteristicPoints <- getCharacteristicPoints(problem, representativeFunction)
#' @export
getCharacteristicPoints <- function(problem, solution) {
  levels <- getLevels(problem$perf)
  offsets <- getOffsets(levels)
  epsilonIndex <- getNrVars(levels)
  altVars <- buildAltVariableMatrix(problem$perf)
  firstCharacteristicPointIndex <- NULL
  linearSegments <- getNrLinearSegments(problem$characteristicPoints)
  if (sum(linearSegments) > 0) {
    firstCharacteristicPointIndex <- getFirstCharacteristicPointIndex(problem)
  }
  
  characteristicPoints <- list()
  
  for (i in seq_len(length(levels))) {
    maximum <- max(problem$perf[, i])
    minimum <- min(problem$perf[, i])
    
    chPoint_x <- c()
    chPoint_y <- c()
    
    if (problem$characteristicPoints[i] != 0) {
      if (problem$criteria[i] == 'g') {
        chPoint_x <- c(minimum)
        chPoint_y <- c(0)
        
        for (j in seq_len(linearSegments[i])) {
          index <- firstCharacteristicPointIndex + j - 1
          
          chPoint_x <- c(chPoint_x, minimum + ((maximum - minimum) * j) / linearSegments[i])
          chPoint_y <- c(chPoint_y, solution$solution[index])
        }
      }
      else {
        for (j in seq_len(linearSegments[i])) {
          index <- firstCharacteristicPointIndex + j - 1
          
          chPoint_x <- c(chPoint_x, minimum + ((maximum - minimum) * (j - 1)) / linearSegments[i])
          chPoint_y <- c(chPoint_y, solution$solution[index])
        }
        
        chPoint_x <- c(chPoint_x, maximum)
        chPoint_y <- c(chPoint_y, 0)
      }
      
      firstCharacteristicPointIndex <- firstCharacteristicPointIndex + linearSegments[i]
    }
    else {
      for (j in seq_len(length(levels[[i]]))) {
        chPoint_x <- c(chPoint_x, levels[[i]][j])
        chPoint_y <- c(chPoint_y, solution$solution[offsets[i] + j - 1])
      }
    }
    
    characteristicPoints[[length(characteristicPoints) + 1]] <- matrix(data = c(chPoint_x, chPoint_y),
                                                                       ncol = 2, byrow = FALSE)
  }
  
  return (characteristicPoints)
}


#' Get assignments
#'
#' This function returns assignments for given model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return Vector of alternative assignments. Each element contains an index
#' of a class that corresponding alternative was assigned to.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getMarginalUtilities}}
#' \code{\link{getThresholds}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' assignments <- getAssignments(problem, representativeFunction)
#' @export
getAssignments <- function(problem, solution) {
  nrAlternatives  = nrow(problem$perf)
  assignments <- array(dim = nrAlternatives)
  firstClAssgnBinVarIndex <- getFirstClAsgnBinVarIndex(problem)
  
  for (i in seq_len(nrAlternatives)) {
    for (j in seq_len(problem$nrClasses)) {
      if (solution$solution[firstClAssgnBinVarIndex + (i - 1) * problem$nrClasses + j - 1] > 0.5) {
        assignments[i] = j
        break
      }
    }
  }
  
  return (assignments)
}

