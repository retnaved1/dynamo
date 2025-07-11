/**
 * @name Indexing with Sensitive Data
 * @description Accessing elements of an array/slice using an index derived from
 *              sensitive data. If this can cause a panic (e.g., index out of bounds)
 *              that is caught and handled differently, or if the panic itself has
 *              a distinguishable timing signature, it might leak information.
 * @kind path-problem
 * @problem.severity warning
 * @id rs/sensitive-indexing-panic
 * @tags security
 *       external/cwe/cwe-208
 *       external/cwe/cwe-200
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.expr.IndexExpr

// Heuristic to identify sensitive data sources (numeric)
class SensitiveNumericDataSourceForIndex extends NewTaintTracking::Configuration {
  SensitiveNumericDataSourceForIndex() { this = "SensitiveNumericDataSourceForIndex" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(offset|index|position|count|size|secret_num).*")
    )
    or
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(offset|index|position|count|size|secret_num).*")
    )
    // Could also include results of arithmetic operations on other sensitive sources
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(IndexExpr idxExpr | sink.asExpr() = idxExpr.getIndex() |
      // Optionally, check if this indexing is within a block that might catch panics.
      // Standard panic catching is via `std::panic::catch_unwind`, but that's harder
      // to model perfectly here without knowing call graph details.
      // For now, we flag any sensitive index operation.
      // A more advanced query could try to trace if `catch_unwind` is used.
      not idxExpr.getArray().getType().isPointer() // Avoid FPs with raw pointer arithmetic if possible
    )
  }

  // No generic sanitizer for indexing itself, bound checks would be sanitizers for the value.
}

from SensitiveNumericDataSourceForIndex config, DataFlow::PathNode source, DataFlow::PathNode sink, IndexExpr idxExpr
where
  config.hasFlowPath(source, sink) and
  sink.asExpr() = idxExpr.getIndex()
select idxExpr, source, sink,
  "Indexing operation at $@ uses sensitive data ($@) as an index. "+
  "If this can cause a panic with distinguishable timing or handling, it might leak information.",
  idxExpr, idxExpr.getLocation().toString(),
  source.getNode().asExpr(), source.getNode().asExpr().toString()
