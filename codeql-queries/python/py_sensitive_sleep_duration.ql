/**
 * @name Sleep duration dependent on sensitive data
 * @description Detects calls to time.sleep() or similar sleep functions where the
 *              sleep duration is derived from sensitive data. This can directly
 *              leak information about the sensitive data through observable time differences.
 * @kind path-problem
 * @problem.severity warning
 * @id py/sensitive-sleep-duration
 * @tags security
 *       external/cwe/cwe-208
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// Heuristic to identify sensitive data sources (could be numeric)
class SensitiveSourceForSleep extends DataFlow::Node {
  SensitiveSourceForSleep() {
    exists(NameNode name | name = this.asName() |
      name.getId().regexpMatch("(?i).*(password|secret|token|key|error_count|retry_delay|user_input_length).*")
    )
    or
    exists(Function f, Parameter param | this.asParameter() = param and f = param.getFunction() |
      f.getName().regexpMatch("(?i).*(process|handle|calculate_delay).*") and
      param.getName().regexpMatch("(?i).*(value|data|input|count|length).*")
    )
    // Could also include results of arithmetic operations on other sensitive sources
  }
}

// Configuration for taint tracking
class SleepDurationConfig extends TaintTracking::Configuration {
  SleepDurationConfig() { this = "SleepDurationConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveSourceForSleep
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(CallNode call |
      // time.sleep(duration)
      (call.getFunction().(AttributeNode).getDefiningAttr().getName() = "sleep" and
       call.getFunction().(AttributeNode).getObject().(NameNode).getId() = "time") or
      // asyncio.sleep(duration)
      (call.getFunction().(AttributeNode).getDefiningAttr().getName() = "sleep" and
       call.getFunction().(AttributeNode).getObject().(NameNode).getId() = "asyncio")
    |
      sink.asCfgNode() = call.getArg(0) // The duration argument
    )
  }
}

from SleepDurationConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, CallNode call
where
  config.hasFlowPath(source, sink) and
  (
    (call.getFunction().(AttributeNode).getDefiningAttr().getName() = "sleep" and
     call.getFunction().(AttributeNode).getObject().(NameNode).getId() = "time") or
    (call.getFunction().(AttributeNode).getDefiningAttr().getName() = "sleep" and
     call.getFunction().(AttributeNode).getObject().(NameNode).getId() = "asyncio")
  ) and
  sink.asCfgNode() = call.getArg(0)
select call, source, sink,
  "Call to sleep function at $@ has its duration dependent on sensitive data ($@), potentially leaking information.",
  call, call.getLocation().toString(),
  source.getNode(), source.getNode().toString()
