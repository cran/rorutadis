

extendModelWithAssignmentComparisonVariables <- function(model, firstAssignmentVariableIndex) {
  numberOfAlternatives <- nrow(model$perfToModelVariables)
  numberOfClasses <- model$nrClasses
  
  firstBinaryVariableIndex <- ncol(model$constraints$lhs) + 1
  
  model$constraints <- addVarialbesToModel(model$constraints, rep("B", numberOfAlternatives * (numberOfAlternatives - 1)))
  nrVariables <- ncol(model$constraints$lhs)
  
  N <- 2 * numberOfClasses
  
  for (i in seq_len(numberOfAlternatives)) {
    for (j in seq_len(numberOfAlternatives)) {
      if (i != j) {
        # c(a_i) - c(a_j) >= 0.5 - N (1 - v_ij) # LB
        # c(a_i) - c(a_j) <= 0.5 + N v_ij # UB
        
        lhsLB <- rep(0, nrVariables)
        lhsUB <- rep(0, nrVariables)
        
        for (h in seq_len(numberOfClasses)) {
          lhsLB[firstAssignmentVariableIndex + (i - 1) * numberOfClasses + h - 1] <- h
          lhsLB[firstAssignmentVariableIndex + (j - 1) * numberOfClasses + h - 1] <- -h
          lhsUB[firstAssignmentVariableIndex + (i - 1) * numberOfClasses + h - 1] <- h
          lhsUB[firstAssignmentVariableIndex + (j - 1) * numberOfClasses + h - 1] <- -h
        }
        
        k <- j
        if (j > i) {
          k <- k - 1
        }
        
        lhsLB[firstBinaryVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- -N
        lhsUB[firstBinaryVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- -N
        
        model$constraints <- combineConstraints(model$constraints, list(lhs = lhsLB, dir = ">=", rhs = 0.5 - N))
        model$constraints <- combineConstraints(model$constraints, list(lhs = lhsUB, dir = "<=", rhs = 0.5))
      }
    }
  }
  
  return (model)
}

#' Find single value function from incomplete preference information
#'
#' This function finds a single value function from incomplete preference information for a problem.
#' 
#' @param problem Problem to investigate.
#' @param stochasticResults Stochastic results (see \code{\link{calculateStochasticResults}}).
#' @param method \code{cai-product}, \code{apoi-product}, or \code{combined-product}.
#' @param reg Reg
#' @param accuracy Accuracy
#' @return List with named elements:
#' \itemize{
#' \item \code{vf} - list of 2-column matrices with marginal value functions (characteristic point in rows),
#' \item \code{thresholds},
#' \item \code{assignments},
#' \item \code{alternativeValues},
#' \item \code{epsilon}.
#' }
#' @seealso
#' \code{\link{calculateStochasticResults}}
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{plotComprehensiveValue}}
#' \code{\link{findSimpleFunction}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' stochasticResults <- calculateStochasticResults(problem, 100)
#' representativeFunction <- findSolutionWithIncomplete(problem, stochasticResults, "cai-product")
#' assignments <- representativeFunction$assignments
#' @export
findSolutionWithIncomplete <- function(problem, stochasticResults, method, reg = 1e-20, accuracy = 1e-10) {
  stopifnot(method %in% c("cai-product", "apoi-product", "combined-product"))
  
  if (!checkConsistency(problem)) {
    stop("Model infeasible.")
  }
  
  model <- buildModel(problem, FALSE)
  
  if (!("B" %in% model$constraints$types)) { # TODO: replace with some better checking
    model <- extendModelWithAssignmentVariables(model)
  }
  
  firstAssignmentVariableIndex <- model$firstThresholdIndex + model$nrClasses - 1

  if (method %in% c("apoi-product", "combined-product")) {
    model <- extendModelWithAssignmentComparisonVariables(model, firstAssignmentVariableIndex)
  }
  
  objective <- rep(0, ncol(model$constraints$lhs))
  
  numberOfAlternatives <- nrow(problem$perf)
  numberOfClasses <- problem$nrClasses
  
  if (method %in% c("cai-product", "combined-product")) {
    for (i in seq_len(numberOfAlternatives)) {
      for (h in seq_len(numberOfClasses)) {
        objective[firstAssignmentVariableIndex + (i - 1) * numberOfClasses + h - 1] <- log(stochasticResults$assignments[i, h] + reg)
      }
    }
  }
  
  if (method %in% c("apoi-product", "combined-product")) {
    firstAssignmentVariableIndex <- firstAssignmentVariableIndex + numberOfClasses * numberOfAlternatives
    
    for (i in seq_len(numberOfAlternatives-1)) {
      for (j in (i+1):numberOfAlternatives) {
        k <- j - 1
        
        apei_ij <- (stochasticResults$preferenceRelation[i, j] + stochasticResults$preferenceRelation[j, i]) - 1.0
        apwi_ij <- stochasticResults$preferenceRelation[i, j] - apei_ij
        apwi_ji <- stochasticResults$preferenceRelation[j, i] - apei_ij
        
        print (c(stochasticResults$preferenceRelation[i, j], stochasticResults$preferenceRelation[j, i], apei_ij, apwi_ij, apwi_ji))
        
        stopifnot(apei_ij > -accuracy && apwi_ij > -accuracy && apwi_ji > -accuracy)
        
        apei_ij <- max(0.0, apei_ij)
        apwi_ij <- max(0.0, apwi_ij)
        apwi_ji <- max(0.0, apwi_ji)
        
        # v_ij  
        objective[firstAssignmentVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- objective[firstAssignmentVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1]  + log(apwi_ij + reg)
        
        # v_ji
        objective[firstAssignmentVariableIndex + (j - 1) * (numberOfAlternatives - 1) + i - 1] <- objective[firstAssignmentVariableIndex + (j - 1) * (numberOfAlternatives - 1) + i - 1] + log(apwi_ji + reg)
        
        # e_ij
        objective[firstAssignmentVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- objective[firstAssignmentVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] - log(apei_ij + reg)
        objective[firstAssignmentVariableIndex + (j - 1) * (numberOfAlternatives - 1) + i - 1] <- objective[firstAssignmentVariableIndex + (j - 1) * (numberOfAlternatives - 1) + i - 1] - log(apei_ij + reg)
      }
    }
  }
  
  solution <- Rglpk_solve_LP(objective, model$constraints$lhs, model$constraints$dir, model$constraints$rhs, max = TRUE,
                        types = model$constraints$types)
  
  return (toSolution(model, solution$solution))
}




