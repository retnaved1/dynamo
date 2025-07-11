/**
 * @name Potentially non-constant time string/slice comparison for sensitive data
 * @description Finds direct string or byte slice comparisons involving potentially
 *              sensitive data, which might be vulnerable to timing attacks.
 *              The standard `==` operator for strings and slices is not constant time.
 * @kind path-problem
 * @problem.severity warning
 * @id go/sensitive-variable-time-comparison
 * @tags security
 *       external/cwe/cwe-208
 */

import go
import semmle.go.dataflow.DataFlow
import semmle.go.dataflow.TaintTracking

// Heuristic to identify sensitive data sources
class SensitiveDataSource extends DataFlow::Node {
  SensitiveDataSource() {
    exists(Parameter p | this.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
      or
      exists(Function f | f = p.getFunction() |
        f.getName().regexpMatch("(?i).*(authenticate|login|verify|authorize|decrypt|check_password).*") and
        p.getName().regexpMatch("(?i).*(password|secret|token|key|data).*")
      )
    )
    or
    // Variables initialized with sensitive-looking names
    exists(Variable v | this.asDefiningExpr(v) instanceof Expr |
        v.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
  }
}

// Configuration for taint tracking
class TimingConfig extends TaintTracking::Configuration {
  TimingConfig() { this = "TimingConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveDataSource
  }

  override predicate isSink(DataFlow::Node sink) {
    // Sink is an operand of a comparison operation (== or !=)
    exists(EqualityTestExpr eq | sink.asExpr() = eq.getAnOperand() |
      not eq.getAnOperand().isConstant() // Exclude comparisons with compile-time constants if desired
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    // Example: calls to crypto/subtle.ConstantTimeCompare or similar
    exists(CallExpr call | call.getTarget().hasQualifiedName("crypto/subtle", "ConstantTimeCompare") |
      node.asExpr() = call.getAnArgument()
    )
  }
}

from TimingConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Comparison involving sensitive data ($@) may not be constant time.",
  source.getNode(), source.getNode().(Expr).toString()
