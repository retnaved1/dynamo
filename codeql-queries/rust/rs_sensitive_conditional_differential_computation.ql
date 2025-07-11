/**
 * @name Branching on sensitive data leading to differential computation
 * @description Detects if expressions where the condition involves sensitive data,
 *              and the branches perform significantly different amounts of computation
 *              (heuristically measured by number of AST nodes or presence of early returns).
 *              This could be exploited in a timing attack.
 * @kind path-problem
 * @problem.severity warning
 * @id rs/sensitive-conditional-differential-computation
 * @tags security
 *       external/cwe/cwe-208
 *       external/cwe/cwe-703
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.expr.IfExpr

// Heuristic to identify sensitive data sources
class SensitiveDataConfigForBranch extends NewTaintTracking::Configuration {
  SensitiveDataConfigForBranch() { this = "SensitiveDataConfigForBranch" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
    or
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(IfExpr ifExpr | sink.asExpr() = ifExpr.getCondition() |
      let thenBlock = ifExpr.getThen() and
      let elseBlockOpt = ifExpr.getElse() in
      (
        // Heuristic: one branch returns, the other doesn't (or doesn't exist)
        (thenBlock.getAChildStmt() instanceof ReturnExpr and
         (not exists(elseBlockOpt) or not elseBlockOpt.getAChildStmt() instanceof ReturnExpr)
        )
        or
        (exists(BlockStmt elseBlock | elseBlock = elseBlockOpt | elseBlock.getAChildStmt() instanceof ReturnExpr) and
         not thenBlock.getAChildStmt() instanceof ReturnExpr
        )
        // Heuristic: significantly different number of statements (very rough proxy)
        // A more detailed analysis would involve counting operations or specific function calls.
        or
        (
          exists(BlockStmt elseBlock | elseBlock = elseBlockOpt |
            count(thenBlock.getAChildStmt()) > 2 * count(elseBlock.getAChildStmt()) or
            count(elseBlock.getAChildStmt()) > 2 * count(thenBlock.getAChildStmt())
          ) and not exists(elseBlockOpt.(BlockStmt).getAChildStmt() instanceof ReturnExpr) // Avoid double counting with return heuristic
             and not thenBlock.getAChildStmt() instanceof ReturnExpr
        )
      )
    )
  }
}

from SensitiveDataConfigForBranch config, DataFlow::PathNode source, DataFlow::PathNode sink, IfExpr ifExpr
where
  config.hasFlowPath(source, sink) and
  sink.asExpr() = ifExpr.getCondition()
select ifExpr, source, sink,
  "Conditional branch at $@ based on sensitive data ($@) may have non-constant time execution due to differing computation or early exit in branches.",
  ifExpr, ifExpr.getLocation().toString(),
  source.getNode().asExpr(), source.getNode().asExpr().toString()
