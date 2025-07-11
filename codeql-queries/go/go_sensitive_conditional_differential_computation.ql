/**
 * @name Branching on sensitive data leading to differential computation
 * @description Detects 'if' statements where the condition involves sensitive data,
 *              and the branches perform significantly different amounts of computation
 *              (heuristically measured by number of statements or presence of early returns).
 *              This could be exploited in a timing attack.
 * @kind path-problem
 * @problem.severity warning
 * @id go/sensitive-conditional-differential-computation
 * @tags security
 *       external/cwe/cwe-208
 *       external/cwe/cwe-703
 */

import go
import semmle.go.dataflow.DataFlow
import semmle.go.dataflow.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveDataSourceForBranch extends DataFlow::Node {
  SensitiveDataSourceForBranch() {
    exists(Parameter p | this.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
    or
    exists(Variable v | this.asDefiningExpr(v) instanceof Expr |
        v.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
  }
}

// Configuration for taint tracking
class ConditionalCompConfig extends TaintTracking::Configuration {
  ConditionalCompConfig() { this = "ConditionalCompConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveDataSourceForBranch
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(IfStmt ifStmt | sink.asExpr() = ifStmt.getCondition() |
      let thenBody = ifStmt.getThen() and
      let elseBody = ifStmt.getElse() in // elseBody can be a BlockStmt or another IfStmt or nil
      (
        // Heuristic: one branch returns, the other doesn't
        (exists(ReturnStmt ret | ret.getParentContainer() = thenBody) and
         (not exists(elseBody) or not exists(ReturnStmt retElse | retElse.getParentContainer() = elseBody))
        )
        or
        (exists(ReturnStmt retElse | retElse.getParentContainer() = elseBody) and
         not exists(ReturnStmt ret | ret.getParentContainer() = thenBody)
        )
        // Heuristic: significantly different number of statements (rough proxy)
        // This is a very basic heuristic.
        or
        (
          exists(BlockStmt thenBlock, BlockStmt elseBlock |
            thenBlock = thenBody and elseBlock = elseBody
          |
            count(thenBlock.getAStmt()) > 2 * count(elseBlock.getAStmt()) or
            count(elseBlock.getAStmt()) > 2 * count(thenBlock.getAStmt())
          ) and
          // Avoid double counting returns if already handled
          not exists(ReturnStmt ret | ret.getParentContainer() = thenBody or ret.getParentContainer() = elseBody)
        )
      )
    )
  }
}

from ConditionalCompConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, IfStmt ifStmt
where
  config.hasFlowPath(source, sink) and
  sink.asExpr() = ifStmt.getCondition()
select ifStmt, source, sink,
  "Conditional branch at $@ based on sensitive data ($@) may have non-constant time execution due to differing computation or early exit in branches.",
  ifStmt, ifStmt.getLocation().toString(),
  source.getNode(), source.getNode().(Expr).toString()
