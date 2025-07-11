/**
 * @name Indexing or Slicing with Sensitive Data
 * @description Accessing elements of a slice/array/string using an index or slice
 *              parameters derived from sensitive data. If this can cause a panic
 *              (e.g., index out of range) that is recovered and handled differently,
 *              or if the panic itself has a distinguishable timing signature, it might
 *              leak information about the sensitive data.
 * @kind path-problem
 * @problem.severity warning
 * @id go/sensitive-indexing-panic
 * @tags security
 *       external/cwe/cwe-208
 *       external/cwe/cwe-200
 */

import go
import semmle.go.dataflow.DataFlow
import semmle.go.dataflow.TaintTracking

// Heuristic to identify sensitive data sources (numeric)
class SensitiveNumericDataSourceForIndexGo extends DataFlow::Node {
  SensitiveNumericDataSourceForIndexGo() {
    exists(Parameter p | this.asParameter() = p |
      p.getName().regexpMatch("(?i).*(offset|index|position|count|size|secret_num).*")
    )
    or
    exists(Variable v | this.asDefiningExpr(v) instanceof Expr |
      v.getName().regexpMatch("(?i).*(offset|index|position|count|size|secret_num).*")
    )
    // Could also include results of arithmetic operations on other sensitive sources
  }
}

// Configuration for taint tracking
class IndexingPanicConfigGo extends TaintTracking::Configuration {
  IndexingPanicConfigGo() { this = "IndexingPanicConfigGo" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveNumericDataSourceForIndexGo
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(IndexExpr idxExpr | sink.asExpr() = idxExpr.getIndex())
    or
    exists(SliceExpr sliceExpr |
      sink.asExpr() = sliceExpr.getLow() or
      sink.asExpr() = sliceExpr.getHigh() or
      sink.asExpr() = sliceExpr.getMax()
    )
    // Optionally, check if this is within a function that has a defer/recover.
    // For now, flag any sensitive index/slice operation.
  }
}

from IndexingPanicConfigGo config, DataFlow::PathNode source, DataFlow::PathNode sink, Expr problematicExpr
where
  config.hasFlowPath(source, sink) and
  (
    problematicExpr.(IndexExpr).getIndex() = sink.asExpr() or
    problematicExpr.(SliceExpr).getLow() = sink.asExpr() or
    problematicExpr.(SliceExpr).getHigh() = sink.asExpr() or
    problematicExpr.(SliceExpr).getMax() = sink.asExpr()
  )
select problematicExpr, source, sink,
  "Indexing/slicing operation at $@ uses sensitive data ($@) as an index/slice component. "+
  "If this can cause a panic with distinguishable timing or handling, it might leak information.",
  problematicExpr, problematicExpr.getLocation().toString(),
  source.getNode(), source.getNode().(Expr).toString()
