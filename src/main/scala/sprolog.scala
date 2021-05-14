import sprolog.Atom.Predicate

import scala.annotation.tailrec
import scala.language.implicitConversions

object sprolog extends App {

  type PartialUpdate[T] = PartialFunction[T, T]

  implicit class PartialSyntax[T](val self: PartialFunction[T, T]) extends AnyVal {
    def applyOrSame[S <: T](t: S): S = self.applyOrElse(t, identity[T]).asInstanceOf[S]
  }

  case class Declaration(name: String, args: List[Atom], body: Expression) {

    def arity: Int = args.size

    def signature: (String, Int) = (name, arity)

    override def toString: String = s"$name(${args mkString ","}) :- $body"

    def updateScope(scope: Int): (Declaration, Int) = {
      var placeholder = 0
      def withScope: PartialUpdate[Atom] = {
        case Atom.Var("_", _) => placeholder += 1; Atom.Var("_", scope + placeholder - 1)
        case Atom.Var(name, _) => Atom.Var(name, scope)
      }
      val nextScope = scope + (if (placeholder == 0) 1 else placeholder)
      Declaration(name, args map (_ transform withScope), body transformNested withScope) -> nextScope
    }
  }

  case class Declarations(decls: Map[(String, Int), List[Declaration]]) {

    def apply(pred: Atom.Predicate): List[Declaration] =
      decls.getOrElse(pred.signature, sys.error(s"Undefined predicate $pred"))
  }
  object Declarations {

    def apply(ds: Seq[Declaration]): Declarations = Declarations(ds.toList.groupBy(_.signature))
  }

  sealed trait Expression {

    override def toString: String = this match {
      case Expression.True => "true"
      case Expression.Fail => "fail"
      case Expression.Call(term) => term.toString
      case Expression.And(first, next) => s"$first, $next"
      case Expression.Or(first, next) => s"($first); ($next)"
      case Expression.Eq(left, right) => s"$left = $right"
    }

    def and(right: Expression): Expression =
      if (right == Expression.True) this
      else if (this == Expression.True) right
      else Expression.And(this, right)

    def or(right: Expression): Expression = Expression.Or(this, right)

    def transform(f: PartialFunction[Atom, Atom]): Expression = this match {
      case Expression.True => this
      case Expression.Call(term) => Expression.Call(f applyOrSame term)
      case Expression.Eq(left, right) => Expression.Eq(f applyOrSame left, f applyOrSame right)
      case Expression.And(first, next) => Expression.And(first transform f, next transform f)
      case Expression.Or(first, next) => Expression.Or(first transform f, next transform f)
    }

    def transformNested(f: PartialFunction[Atom, Atom]): Expression = transform(_ transform f)
  }
  object Expression {

    case object True extends Expression
    case object Fail extends Expression
    case class Call(predicate: Predicate) extends Expression
    case class Eq(left: Atom, right: Atom) extends Expression
    case class And(first: Expression, next: Expression) extends Expression
    case class Or(first: Expression, next: Expression) extends Expression
  }

  sealed trait Atom {

    override def toString: String = this match {
      case Atom.Var(name, 0) => name
      case Atom.Var(name, scope) => s"$name$scope"
      case Atom.Symbol(name) => name
      case Atom.Predicate(".", head :: tail :: Nil) =>
        def showTail: Atom => String = {
          case Atom.Symbol("[]") => ""
          case Atom.Predicate(".", head :: tail :: Nil) => s", $head${showTail(tail)}"
          case other => s"|$other"
        }
        s"[$head${showTail(tail)}]"

      case Atom.Predicate(name, args) => s"$name(${args mkString ","})"
    }

    def transform(f: PartialFunction[Atom, Atom]): Atom = this match {
      case Atom.Predicate(name, args) => Atom.Predicate(name, args.map(_ transform f))
      case other => f applyOrSame other
    }
  }
  sealed trait Value extends Atom
  object Atom {
    case class Var(name: String, scope: Int = 0) extends Atom
    case class Symbol(name: String) extends Value
    case class Predicate(name: String, args: List[Atom] = Nil) extends Value {
      def arity: Int = args.size
      def signature: (String, Int) = (name, arity)
    }
  }

  object syntax {

    implicit def str2atom(value: String): Atom =
      if (Character.isUpperCase(value.head) || value == "_") Atom.Var(value)
      else Atom.Symbol(value)

    implicit def predicate2expression(term: Predicate): Expression = Expression.Call(term)

    implicit def predicate2declaration(pred: Atom.Predicate): Declaration =
      Declaration(pred.name, pred.args, Expression.True)

    implicit class CallSyntax(val self: String) extends AnyVal {
      def !(args: Atom*): Atom.Predicate = Atom.Predicate(self, args.toList)
    }

    implicit class DeclSyntax(val self: Atom.Predicate) extends AnyVal {
      def := (body: Expression): Declaration = Declaration(self.name, self.args, body)
    }

    implicit class DeclZeroSyntax(val self: String) extends AnyVal {
      def := (body: Expression): Declaration = Declaration(self, Nil, body)
    }

    implicit class AtomSyntax(val self: Atom) extends AnyVal {
      def === (right: Atom): Expression = Expression.Eq(self, right)
    }

    object List {
      val Nil: Atom = "[]"
      def cons(head: Atom, tail: Atom): Atom = "."!(head, tail)
      def apply(xs: Atom*): Atom = xs.foldRight[Atom](Nil)(cons)
    }
  }

  case class Env(
    bindings: Map[Atom.Var, Value] = Map.empty,
    equivalent: List[Set[Atom.Var]] = Nil,
    scope: Int = 1
  ) {
    def equivOf(v: Atom.Var): Set[Atom.Var] = equivalent.find(_ contains v) getOrElse Set(v)
    def equiv(a: Atom.Var, b: Atom.Var): Env = {
      val eq = equivOf(a) ++ equivOf(b)
      val rest = equivalent.filter(s => !s(a) && !s(b))
      copy(
        equivalent = eq :: rest,
        bindings = bindings.get(a) orElse bindings.get(b) match {
          case None => bindings
          case Some(v) => bindings ++ eq.map(_ -> v)
        }
      )
    }
    def bind(v: Atom.Var, value: Value): Env = copy(
      bindings = bindings + (v -> value) ++ equivOf(v).map(_ -> value)
    )
    def resolve(value: Value): Value = resolve(value: Atom).asInstanceOf[Value]
    def resolve(value: Atom): Atom = value match {
      case s: Atom.Symbol => s
      case Atom.Predicate(name, args) => Atom.Predicate(name, args map resolve)
      case v: Atom.Var => bindings.get(v).fold[Atom](v)(resolve)
    }
    def resolve(expr: Expression): Expression = expr match {
      case Expression.Call(pred) => Expression.Call(resolve(pred).asInstanceOf[Atom.Predicate])
      case Expression.And(l, r) => Expression.And(resolve(l), resolve(r))
      case Expression.Or(l, r) => Expression.Or(resolve(l), resolve(r))
      case e => e
    }
    def debug(): Unit = {
      for (e <- equivalent) {
        val value = bindings.get(e.head).fold("")(v => s" <- $v")
        println(s"${e mkString " = "}$value")
      }
      for ((v, value) <- bindings if !equivalent.exists(_ contains v)) {
        println(s"$v <- $value")
      }
    }
  }

  sealed trait EvalStack

  case class Solution(
    declarations: Declarations,
    env: Env = Env(),
    expressions: List[Expression] = Nil,
    exploreLater: List[(Env, Expression)] = (Env(), Expression.Fail) :: Nil,
    results: List[Map[Atom.Var, Value]] = Nil,
    question: Set[Atom.Var] = Set.empty
  ) {
    def isFinished: Boolean = expressions.isEmpty && exploreLater.isEmpty

    def currentState: Option[Boolean] =
      if (expressions.isEmpty) Some(true)
      else if (expressions.head == Expression.Fail) Some(false)
      else None

    def debugDeclarations(): Unit = {
      println("--- Knowledge:")
      for (((name, arity), decls) <- declarations.decls) {
        println()
        println(s"$name/$arity")
        decls.foreach(println(_))
      }
      println(s"? ${question mkString ", "}")
    }

    def debug(): Unit = {
      println(s"\n--- Expr: ${expressions.map(env.resolve) mkString ", "}")
      env.debug()
      if (exploreLater.size > 1) {
        println(s"--- Explore later:")
        exploreLater.init.foreach(p => println(p._2))
      }
    }

    def exploreNext(success: Boolean): Solution = {
      val updatedResults =
        if (!success || env.bindings.isEmpty) results
        else env.bindings.transform((_, v) => env.resolve(v)) :: results
      exploreLater match {
        case (env, expr) :: rest => copy(
          expressions = expr :: Nil,
          exploreLater = rest,
          env = env,
          results = updatedResults
        )
        case Nil => copy(
          expressions = Nil,
          env = Env(),
          results = updatedResults
        )
      }
    }

    def next: Solution = next(expressions)

    @tailrec private def next(expressions: List[Expression]): Solution = expressions match {
      case Nil =>
        exploreNext(success = true)

      case Expression.True :: rest =>
        next(rest)

      case Expression.Fail :: _ =>
        exploreNext(success = false)

      case Expression.Or(first, next) :: rest => copy(
        expressions = first :: rest,
        exploreLater = (env, rest.foldLeft(next)(_ and _)) :: exploreLater
      )

      case Expression.And(first, next) :: rest =>
        this.next(first :: next :: rest)

      case Expression.Call(predicate) :: rest =>
        val next = declarations(predicate)
          .map(_ updateScope env.scope)
          .flatMap {
            case (Declaration(_, args, body), nextScope) =>
              unifyAll(args zip predicate.args, env).map { env =>
                env.copy(scope = nextScope) -> body
              }
          }
        next match {
          case (env, expr) :: todo => copy(
            expressions = expr :: rest,
            env = env,
            exploreLater = todo ++ exploreLater
          )
          case Nil => copy(expressions = Expression.Fail :: Nil)
        }

      case Expression.Eq(left, right) :: rest => unify(left, right, env) match {
        case Some(env) => copy(expressions = rest, env = env)
        case None => copy(expressions = Expression.Fail :: Nil)
      }
    }

    def unify(a: Atom, b: Atom, env: Env): Option[Env] = (a, b) match {
      case (`a`, `a`) => Some(env)
      case (v: Atom.Var, value) => bind(v, value, env)
      case (value, v: Atom.Var) => bind(v, value, env)
      case (p1: Atom.Predicate, p2: Atom.Predicate) if p1.signature == p2.signature =>
        unifyAll(p1.args zip p2.args, env)
      case _ => None
    }

    def unifyAll(pairs: List[(Atom, Atom)], env: Env): Option[Env] = pairs.foldLeft(Option(env)) {
      case (prev, (a, b)) => prev.flatMap(env => unify(a, b, env))
    }

    def bind(v: Atom.Var, value: Atom, env: Env): Option[Env] = value match {
      case v2: Atom.Var => (env.bindings.get(v), env.bindings.get(v2)) match {
        case (Some(a), Some(b)) => unify(a, b, env)
        case _ => Some(env.equiv(v, v2))
      }
      case b: Value => env.bindings.get(v) match {
        case Some(a) => unify(a, b, env)
        case None => Some(env.bind(v, b))
      }
    }

    def currentAnswer: Map[Atom.Var, Value] = env.bindings.filter(question contains _._1)

    def answers: List[Map[Atom.Var, Value]] = results.map(_.filter(question contains _._1))
  }

  object Solution {

    def apply(ds: Declaration*): Solution = {
      val decls = Declarations(ds)
      val question = decls(Atom.Predicate("?"))
      var questionVars = Set.empty[Atom.Var]
      question.foreach(_.body transformNested {
        case v: Atom.Var =>
          questionVars += v
          v
      })
      new Solution(
        declarations = decls,
        expressions = question.map(_.body).reduce(_ or _) :: Nil,
        question = questionVars
      )
    }
  }

  locally {
    import syntax._
    val solution = Solution(
      "parent"!("alice", "bob"),
      "parent"!("bob", "mary"),
      "ancestor"!("X", "Y") := "parent"!("X", "Y"),
      "ancestor"!("X", "Y") := ("parent"!("X", "Z") and "ancestor"!("Z", "Y")),
//      "?" := "ancestor"!("alice", "X")
      "member"!("X", "cons"!("X", "_")),
      "member"!("X", "cons"!("H", "T")) := "member"!("X", "T"),
//      "?" := "member"!("2", "cons"!("1", "cons"!("2", "cons"!("3", "[]"))))
      "reverse"!("I", "O") := "reverse"!("I", List.Nil, "O"),
      "reverse"!(List.Nil, "A", "A"),
      "reverse"!(List.cons("H", "T"), "A", "O") := "reverse"!("T", List.cons("H", "A"), "O"),
//      "?" := "reverse"!(List("1", "2", "3"), "X"),
//      "?" := "reverse"!(List("1", "2"), List("2", "3"))
      // hanoi(Piles, From, To, Third, Moves)
      "hanoi"!(List.Nil, "_", "_", "_", List.Nil),
      "hanoi"!(List("_"), "A", "B", "C", List("A", "B")),
      "hanoi"!(List.cons("H", "T"), "A", "B", "C", "R") := (
        "hanoi"!("T", "A", "C", "B", "R1") and "hanoi"!(List("H"), "A", "B", "C", "R2") and
        "hanoi"!("T", "C", "B", "A", "R3") and "concat"!("R2", "R3", "R23") and "concat"!("R1", "R23", "R")
      ),
      "concat"!("A", "B", "AB") := "concat"!("A", List.Nil, "B", "AB"),
      "concat"!(List.cons("H", "T"), "R", "B", "AB") := "concat"!("T", List.cons("H", "R"), "B", "AB"),
      "concat"!(List.Nil, List.cons("H", "T"), "B", "AB") := "concat"!(List.Nil, "T", List.cons("H", "B"), "AB"),
      "concat"!(List.Nil, List.Nil, "AB", "AB"),
      // ?
//      "?" := "hanoi"!(List("1", "2", "3"), "a", "b", "c", "Moves")
      "?" := "concat"!(List("1", "2"), "B", List("1", "2", "3", "4"))
    )
    solution.debugDeclarations()
    Iterator.iterate(solution)(_.next)
      .zipWithIndex
      .map {
        case (current, i) =>
          println(s"\n------- Step $i -------------------------------------------------------")
          current.debug()
          val answer = current.currentState
          if (answer.nonEmpty) {
            println(s"### Result: ${if (answer contains true) "SUCCESS" else "FAILURE"}")
            for ((Atom.Var(name, _), value) <- current.currentAnswer)
              println(s"  $name = $value")
            println()
          }
          current
      }
      .take(1000)
      .find(_.isFinished)
      .foreach { res =>
        println("------- Answers -------")
        for ((answer, i) <- res.answers.zipWithIndex) {
          println(s"${i + 1}. ${answer.map { case (v, value) => s"${v.name} = $value" } mkString ", " }")
        }
        println("-----------------------")
      }
  }
}
