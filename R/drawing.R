#### DRAWING PLOTS

#' Draw marginal value functions and chart of alternative utilities
#'
#' This function draws marginal value functions and alternative utilities chart.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @param printLabels Whether print alternatives identifiers on marginal value
#' function plots and utility values on alternative utility chart or not
#' (default \code{TRUE}).
#' @param criteria Vector containing  \emph{0} for utility chart and/or indices
#' of criteria for which marginal value functions should be plotted.
#' If this parameter was \code{NULL} functions for all criteria and utility chart
#' will be plotted (default \code{NULL}).
#' @param plotsPerRow Number of plots per row (default \code{2}).
#' @param descending Mode of sorting alternatives on utility chart:
#' \itemize{
#' \item \code{NULL} - unsorted, preserved \code{problem$perf} order,
#' \item \code{TRUE} - sorted descending by value of utility,
#' \item \code{FALSE} - sorted ascending by value of utility.
#' }
#' 
#' @return Plot.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('c', 'g'), c(3, 3))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' drawUtilityPlots(problem, representativeFunction)
#' @import ggplot2
#' @import gridExtra
#' @export
drawUtilityPlots <- function(problem, solution, printLabels = TRUE,
                             criteria = NULL, plotsPerRow = 2,
                             descending = NULL) {
  stopifnot(is.logical(printLabels))
  stopifnot(plotsPerRow > 0)
  stopifnot(length(which(criteria < 0)) == 0)
  a <- NULL
  U <- NULL
  
  if (is.null(criteria)) {
    criteria <- c(1:ncol(problem$perf), 0)
  }
  
  graphs <- vector("list", length(criteria))
  
  altVars <- buildAltVariableMatrix(problem$perf)
  marginalUtilities <- getMarginalUtilities(problem, solution)
  characteristicPoints <- getCharacteristicPoints(problem, solution)
  labels <- rownames(problem$perf)
  
  if (is.null(labels)) {
    labels <- paste("a", 1:nrow(problem$perf), sep = "")
  }

  for (index in seq_len(length(criteria))) {
    if (criteria[index] == 0) {
      df <- data.frame(a = labels,
                       U = sapply(1:nrow(problem$perf),
                                  function(x) { sum(marginalUtilities[x, ]) } ))
               
      graphs[[index]] <- ggplot(data = df, aes(x = a, y = U)) +
        geom_bar(stat = "identity") +
        xlab("alternative") +
        ylab("U") +
        theme_bw(base_size = 20) +
        expand_limits(y = 1.05) +
        theme(axis.text.x = element_text(angle = 45, hjust = 1))
      
      if (is.null(descending) == FALSE) {
        if (descending) {
          graphs[[index]] <- graphs[[index]] +
            scale_x_discrete(limits = df[with(df, order(-U)), ]$a)
        }
        else {
          graphs[[index]] <- graphs[[index]] +
            scale_x_discrete(limits = df[with(df, order(U)), ]$a)
        }
      }
      
      if (printLabels) {
        graphs[[index]] <- graphs[[index]] + geom_text(aes(a, U, label = round(U, 2)),
                                                       size = 5,
                                                       hjust = 0.5,
                                                       vjust = -0.1,
                                                       angle = 0)
      }
    }
    else {
      i = criteria[index]
      
      
      g = u = l = c()
      
      for (j in seq_len(nrow(problem$perf))) {
        rowFound <- FALSE
        
        for (k in seq_len(length(g))) {
          if (g[k] == problem$perf[j, i] && u[k] == marginalUtilities[j, i]) {
            l[k] <- paste(l[k], labels[j], sep=", ")
            rowFound <- TRUE
            break
          }
        }
        
        if (rowFound == FALSE) {
          g = c(g, problem$perf[j, i])
          u = c(u, marginalUtilities[j, i])
          l = c(l, labels[j])
        }
      }
      
      df <- data.frame(g = g, u = u, l = l)
      
      graphs[[index]] <- ggplot(df, aes(x = g, y = u)) + 
        geom_point(size = 3) +
        xlab(paste("g", i, sep = "")) +
        ylab(paste("u", i, sep = "")) +
        theme_bw(base_size = 20)
      
      if (printLabels) {
        graphs[[index]] <- graphs[[index]] + geom_text(aes(g, u, label = l),
                                               size = 5,
                                               hjust = sapply(unlist(df['u']),
                                                              function(x) {if(x < max(df['u'])/2.0) return (-0.1) else return (1.1)}),
                                               vjust = 0.25,
                                               angle = 90)
      }
      
      if (problem$characteristicPoints[i] > 0) {
        pointsDf = data.frame(g = unlist(characteristicPoints[[i]][, 1]),
                        u = unlist(characteristicPoints[[i]][, 2]))
        graphs[[index]] <- graphs[[index]] + 
          geom_line(data = pointsDf, aes(x = g, y = u), colour = "grey20")
      }
    }
  }
  
  nCol <- max(floor(sqrt(length(graphs))), plotsPerRow)
  
  grid.arrange(do.call(arrangeGrob, c(graphs, list(ncol = nCol))))
}
