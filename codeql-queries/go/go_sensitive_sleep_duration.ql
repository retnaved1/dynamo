/**
 * @name Sleep duration dependent on sensitive data
 * @description Detects calls to `time.Sleep()` where the sleep duration is
 *              derived from sensitive data. This can directly leak information
 *              about the sensitive data through observable time differences.
 * @kind path-problem
 * @problem.severity warning
 * @id go/sensitive-sleep-duration
 * @tags security
 *       external/cwe/cwe-208
 */

import go
import semmle.go.dataflow.DataFlow
import semmle.go.dataflow.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveDataSourceForSleepGo extends DataFlow::Node {
  SensitiveDataSourceForSleepGo() {
    exists(Parameter p | this.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|error_count|retry_delay|input_length).*")
    )
    or
    exists(Variable v | this.asDefiningExpr(v) instanceof Expr |
      v.getName().regexpMatch("(?i).*(delay|duration|count|length).*")
    )
  }
}

// Configuration for taint tracking
class SleepDurationConfigGo extends TaintTracking::Configuration {
  SleepDurationConfigGo() { this = "SleepDurationConfigGo" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveDataSourceForSleepGo
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(CallExpr call |
      call.getTarget().hasQualifiedName("time", "Sleep") and
      sink.asExpr() = call.getArgument(0) // The duration argument
    )
  }
}

from SleepDurationConfigGo config, DataFlow::PathNode source, DataFlow::PathNode sink, CallExpr call
where
  config.hasFlowPath(source, sink) and
  call.getTarget().hasQualifiedName("time", "Sleep") and
  sink.asExpr() = call.getArgument(0)
select call, source, sink,
  "Call to time.Sleep() at $@ has its duration dependent on sensitive data ($@), potentially leaking information.",
  call, call.getLocation().toString(),
  source.getNode(), source.getNode().(Expr).toString()
