/**
 * @name Sleep duration dependent on sensitive data
 * @description Detects calls to `std::thread::sleep`, `tokio::time::sleep` or similar
 *              sleep functions where the sleep duration is derived from sensitive data.
 *              This can directly leak information about the sensitive data.
 * @kind path-problem
 * @problem.severity warning
 * @id rs/sensitive-sleep-duration
 * @tags security
 *       external/cwe/cwe-208
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.expr.CallExpr

// Heuristic to identify sensitive data sources
class SensitiveDataSourceForSleepRust extends NewTaintTracking::Configuration {
  SensitiveDataSourceForSleepRust() { this = "SensitiveDataSourceForSleepRust" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|error_count|retry_delay|input_length).*")
    )
    or
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(delay|duration|count|length).*")
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(CallExpr call |
      (
        call.getFullyQualifiedName().matches("std::thread::sleep") or
        call.getFullyQualifiedName().matches("tokio::time::sleep")
        // Could add other crates' sleep functions here
      ) and
      // The duration is usually the first argument, often wrapped in Duration::from_millis or similar
      exists(Expr arg | arg = call.getAnArgument() | sink.asExpr() = arg or sink.asExpr() = arg.getAChildExpr*())
    )
  }
}

from SensitiveDataSourceForSleepRust config, DataFlow::PathNode source, DataFlow::PathNode sink, CallExpr call
where
  config.hasFlowPath(source, sink) and
  (
    call.getFullyQualifiedName().matches("std::thread::sleep") or
    call.getFullyQualifiedName().matches("tokio::time::sleep")
  ) and
  exists(Expr arg | arg = call.getAnArgument() | sink.asExpr() = arg or sink.asExpr() = arg.getAChildExpr*())
select call, source, sink,
  "Call to sleep function at $@ has its duration potentially dependent on sensitive data ($@).",
  call, call.getLocation().toString(),
  source.getNode().asExpr(), source.getNode().asExpr().toString()
