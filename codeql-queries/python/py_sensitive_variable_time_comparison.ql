/**
 * @name Potentially non-constant time string comparison for sensitive data
 * @description Finds direct string comparisons involving potentially sensitive data,
 *              which might be vulnerable to timing attacks.
 * @kind path-problem
 * @problem.severity warning
 * @id py/sensitive-variable-time-comparison
 * @tags security
 *       external/cwe/cwe-208
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveSource extends DataFlow::Node {
  SensitiveSource() {
    exists(NameNode name | name = this.asName() |
      name.getId().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
    or
    // Parameters of functions that might handle sensitive data
    exists(Function f, Parameter param | this.asParameter() = param and f = param.getFunction() |
      f.getName().regexpMatch("(?i).*(authenticate|login|verify|authorize|decrypt|check_password).*") and
      param.getName().regexpMatch("(?i).*(password|secret|token|key|data).*")
    )
  }
}

// Configuration for taint tracking
class TimingConfig extends TaintTracking::Configuration {
  TimingConfig() { this = "TimingConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveSource
  }

  override predicate isSink(DataFlow::Node sink) {
    // Sink is a direct comparison operation
    exists(CompareNode comp | sink.asCfgNode() = comp.getAnOperand() |
      comp.getOp(0) instanceof Eq or
      comp.getOp(0) instanceof NotEq or
      comp.getOp(0) instanceof Is or // Less common for timing but possible
      comp.getOp(0) instanceof IsNot // Less common for timing but possible
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    // Example: Explicit constant-time comparison functions (if any were identified)
    // exists(CallNode call | call.getFunction().getName() = "constant_time_compare" and node = call.getArg(0))
    none() // No generic sanitizers for this example
  }
}

from TimingConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Comparison involving sensitive data ($@) may not be constant time.",
  source.getNode(), source.getNode().getName()
