/**
 * @name Indexing or Slicing with Sensitive Data
 * @description Accessing elements of a list/string using an index or slice derived
 *              from sensitive data. If this can cause exceptions (e.g., IndexError)
 *              that are handled differently or have different processing times,
 *              it might leak information about the sensitive data.
 * @kind path-problem
 * @problem.severity warning
 * @id py/sensitive-indexing-exception
 * @tags security
 *       external/cwe/cwe-208
 *       external/cwe/cwe-200
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// Heuristic to identify sensitive data sources (especially those that might be numeric or used as indices)
class SensitiveNumericSource extends DataFlow::Node {
  SensitiveNumericSource() {
    exists(NameNode name | name = this.asName() |
      name.getId().regexpMatch("(?i).*(offset|index|position|count|len|size|secret_num).*")
    )
    or
    exists(Function f, Parameter param | this.asParameter() = param and f = param.getFunction() |
      f.getName().regexpMatch("(?i).*(process|get_element|lookup).*") and
      param.getName().regexpMatch("(?i).*(idx|offset|pos|num).*")
    )
    // Could also include results of arithmetic operations on other sensitive sources
  }
}

// Configuration for taint tracking
class IndexingConfig extends TaintTracking::Configuration {
  IndexingConfig() { this = "IndexingConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveNumericSource
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(Subscript sub |
      (sink.asCfgNode() = sub.getIndex() or sink.asCfgNode() = sub.getLower() or sink.asCfgNode() = sub.getUpper()) and
      // Check if this subscript is within a try-except block that catches IndexError or generic Exception
      exists(Try tryStmt, Name handlerType |
        tryStmt.getAStmt().getAstNode() = sub.getScope().getAstNode() and // Subscript is in try body
        tryStmt.getAHandler().getType().(NameNode).getId() = handlerType.getId() and
        (handlerType.getId() = "IndexError" or handlerType.getId() = "LookupError" or handlerType.getId() = "Exception")
      )
    )
  }
}

from IndexingConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, Subscript sub
where
  config.hasFlowPath(source, sink) and
  (sink.asCfgNode() = sub.getIndex() or sink.asCfgNode() = sub.getLower() or sink.asCfgNode() = sub.getUpper()) and
  exists(Try tryStmt | tryStmt.getAStmt().getAstNode() = sub.getScope().getAstNode()) // Simplified: just check if it's in any try block for now
select sub, source, sink,
  "Indexing/slicing operation at $@ uses sensitive data ($@) as an index/slice component. "+
  "If this can cause exceptions handled differently, it might leak information.",
  sub, sub.getLocation().toString(),
  source.getNode(), source.getNode().toString()
