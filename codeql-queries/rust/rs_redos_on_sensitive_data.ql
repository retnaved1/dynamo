/**
 * @name Regular expression matching on sensitive data with 'regex' crate
 * @description Finds calls to functions from the 'regex' crate (e.g., Regex::is_match, Regex::find)
 *              where the input string is derived from sensitive data.
 *              While Rust's 'regex' crate is generally ReDoS-safe, complex patterns or specific
 *              use cases might still warrant review for performance characteristics when handling sensitive input.
 * @kind path-problem
 * @problem.severity info
 * @id rs/redos-on-sensitive-data
 * @tags security
 *       external/cwe/cwe-1333 // ReDoS (by analogy)
 *       external/cwe/cwe-208  // Timing Attack (indirectly)
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.expr.MethodCallExpr

// Heuristic to identify sensitive data sources
class SensitiveTextDataSourceRust extends NewTaintTracking::Configuration {
  SensitiveTextDataSourceRust() { this = "SensitiveTextDataSourceRust" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth|user_input|query|payload).*")
    )
    or
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(user_input|raw_payload|unescaped_query).*")
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(MethodCallExpr call |
      // methods on Regex objects: is_match, find, captures, etc.
      call.getReceiverType().hasQualifiedName("regex", "Regex") and
      call.getMethodName().regexpMatch("is_match|find|captures|find_iter|captures_iter|split|replace|replace_all") and
      sink.asExpr() = call.getArgument(0) // The text to search
    )
  }
}

from SensitiveTextDataSourceRust config, DataFlow::PathNode source, DataFlow::PathNode sink, MethodCallExpr call
where
  config.hasFlowPath(source, sink) and
  call.getReceiverType().hasQualifiedName("regex", "Regex") and
  call.getMethodName().regexpMatch("is_match|find|captures|find_iter|captures_iter|split|replace|replace_all") and
  sink.asExpr() = call.getArgument(0)
select call, source, sink,
  "Call to regex method at $@ uses sensitive data ($@) as input. Review regex pattern and context for potential performance issues.",
  call, call.getLocation().toString(),
  source.getNode().asExpr(), source.getNode().asExpr().toString()
