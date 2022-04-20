package org.checkerframework.checker.dividebyzero;

import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import java.lang.annotation.Annotation;

import java.util.*;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroTransfer extends CFTransfer {

    enum Comparison {
        /** == */ EQ,
        /** != */ NE,
        /** <  */ LT,
        /** <= */ LE,
        /** >  */ GT,
        /** >= */ GE
    }

    enum BinaryOperator {
        /** + */ PLUS,
        /** - */ MINUS,
        /** * */ TIMES,
        /** / */ DIVIDE,
        /** % */ MOD
    }

    int getIndexOfAnnotation(AnnotationMirror annotation) {
        ArrayList<Class<? extends Annotation>> cls = new ArrayList<>(Arrays.asList(
                MinusTwo.class,
                MinusOne.class,
                Zero.class,
                One.class,
                Two.class,
                LTZero.class,
                LEZero.class,
                GTZero.class,
                GEZero.class,
                NotZero.class,
                Top.class,
                Bottom.class));
        for (int i = 0; i < cls.size(); ++i) {
            if (equal(annotation, reflect(cls.get(i)))) {
                return i;
            }
        }
        return -1;
    }

    AnnotationMirror minusTwoAM = reflect(MinusTwo.class);
    AnnotationMirror minusOneAM = reflect(MinusOne.class);
    AnnotationMirror zeroAM = reflect(Zero.class);
    AnnotationMirror oneAM = reflect(One.class);
    AnnotationMirror twoAM = reflect(Two.class);
    AnnotationMirror lt0AM = reflect(LTZero.class);
    AnnotationMirror le0AM = reflect(LEZero.class);
    AnnotationMirror gt0AM = reflect(GTZero.class);
    AnnotationMirror ge0AM = reflect(GEZero.class);

    AnnotationMirror not0AM = reflect(NotZero.class);

    private boolean inList(AnnotationMirror x, Collection<Class<? extends Annotation>> y) {
        for (Class<? extends Annotation> c : y) {
            if (equal(x, reflect(c))) {
                return true;
            }
        }
        return false;
    }

    private boolean isConst(AnnotationMirror x) {
        return inList(x, new ArrayList<>(Arrays.asList(
                MinusTwo.class, MinusOne.class, Zero.class, One.class, Two.class)));
    }

    AnnotationMirror refineWithRules(AnnotationMirror[][] rules, AnnotationMirror lhs, AnnotationMirror rhs) {
        if (equal(lhs, bottom()) || equal(rhs, bottom())) {
            return bottom();
        }
        if (isConst(lhs)) {
            return lhs;
        }
        return rules[getIndexOfAnnotation(lhs) - 5][getIndexOfAnnotation(rhs)];
    }


    // ========================================================================
    // Transfer functions to implement

    //       MinusTwo  MinusOne  Zero      One       Two     LTZero    LEZero    GTZero  GEZero  NotZero Top
    AnnotationMirror[][] ltRefinements = {
            {lt0AM,    lt0AM,    lt0AM,    lt0AM,    lt0AM,  lt0AM,    lt0AM,    lt0AM,  lt0AM,  lt0AM,  lt0AM}, // LTZero < *
            {lt0AM,    lt0AM,    lt0AM,    le0AM,    le0AM,  lt0AM,    lt0AM,    le0AM,  le0AM,  le0AM,  le0AM}, // LEZero < *
            {bottom(), bottom(), bottom(), bottom(), oneAM,  bottom(), bottom(), gt0AM,  gt0AM,  gt0AM,  gt0AM}, // GTZero < *
            {bottom(), bottom(), bottom(), zeroAM,   ge0AM,  bottom(), bottom(), ge0AM,  ge0AM,  ge0AM,  ge0AM}, // GEZero < *
            {lt0AM,    lt0AM,    lt0AM,    lt0AM,    not0AM, lt0AM,    lt0AM,    not0AM, not0AM, not0AM, not0AM}, // NotZero < *
            {lt0AM,    lt0AM,    lt0AM,    le0AM,    top(),  lt0AM,    lt0AM,    top(),  top(),  top(),  top()}  // Top < *
    };

    //       MinusTwo  MinusOne  Zero      One     Two     LTZero    LEZero    GTZero  GEZero  NotZero Top
    AnnotationMirror[][] leRefinements = {
            {lt0AM,    lt0AM,    lt0AM,    lt0AM,  lt0AM,  lt0AM,    lt0AM,    lt0AM,  lt0AM,  lt0AM,  lt0AM}, // LTZero <= *
            {lt0AM,    lt0AM,    le0AM,    le0AM,  le0AM,  lt0AM,    le0AM,    le0AM,  le0AM,  le0AM,  le0AM}, // LEZero <= *
            {bottom(), bottom(), bottom(), oneAM,  gt0AM,  bottom(), bottom(), gt0AM,  gt0AM,  gt0AM,  gt0AM}, // GTZero <= *
            {bottom(), bottom(), zeroAM,   ge0AM,  ge0AM,  bottom(), zeroAM,   ge0AM,  ge0AM,  ge0AM,  ge0AM}, // GEZero <= *
            {lt0AM,    lt0AM,    lt0AM,    not0AM, not0AM, lt0AM,    lt0AM,    not0AM, not0AM, not0AM, not0AM}, // NotZero <= *
            {lt0AM,    lt0AM,    le0AM,    top(),  top(),  lt0AM,    le0AM,    top(),  top(),  top(),  top()}  // Top <= *
    };

    //       MinusTwo    MinusOne  Zero      One       Two       LTZero  LEZero  GTZero    GEZero    NotZero Top
    AnnotationMirror[][] gtRefinements = {
            {minusOneAM, bottom(), bottom(), bottom(), bottom(), lt0AM,  lt0AM,  bottom(), bottom(), lt0AM,  lt0AM}, // LTZero > *
            {le0AM,      zeroAM,   bottom(), bottom(), bottom(), le0AM,  le0AM,  bottom(), bottom(), le0AM,  le0AM}, // LEZero > *
            {gt0AM,      gt0AM,    gt0AM,    gt0AM,    gt0AM,    gt0AM,  gt0AM,  gt0AM,    gt0AM,    gt0AM,  gt0AM}, // GTZero > *
            {ge0AM,      ge0AM,    gt0AM,    gt0AM,    gt0AM,    ge0AM,  ge0AM,  gt0AM,    gt0AM,    ge0AM,  ge0AM}, // GEZero > *
            {not0AM,     gt0AM,    gt0AM,    gt0AM,    gt0AM,    not0AM, not0AM, gt0AM,    gt0AM,    not0AM, not0AM}, // NotZero > *
            {top(),      ge0AM,    gt0AM,    gt0AM,    gt0AM,    top(),  top(),  gt0AM,    gt0AM,    top(),  top()}, // Top > *
    };

    //       MinusTwo MinusOne    Zero      One       Two       LTZero  LEZero  GTZero    GEZero    NotZero Top
    AnnotationMirror[][] geRefinements = {
            {lt0AM,   minusOneAM, bottom(), bottom(), bottom(), lt0AM,  lt0AM,  bottom(), bottom(), lt0AM,  lt0AM}, // LTZero >= *
            {le0AM,   le0AM,      zeroAM,   bottom(), bottom(), le0AM,  le0AM,  bottom(), zeroAM,   le0AM,  le0AM}, // LEZero >= *
            {gt0AM,   gt0AM,      gt0AM,    gt0AM,    gt0AM,    gt0AM,  gt0AM,  gt0AM,    gt0AM,    gt0AM,  gt0AM}, // GTZero >= *
            {ge0AM,   ge0AM,      ge0AM,    gt0AM,    gt0AM,    ge0AM,  ge0AM,  gt0AM,    ge0AM,    ge0AM,  ge0AM}, // GEZero >= *
            {not0AM,  not0AM,     gt0AM,    gt0AM,    gt0AM,    not0AM, not0AM, gt0AM,    gt0AM,    not0AM, not0AM}, // NotZero >= *
            {top(),   top(),      ge0AM,    gt0AM,    gt0AM,    top(),  top(),  gt0AM,    ge0AM,    top(),  top()}  // Top >= *
    };

    //       MinusTwo MinusOne Zero    One     Two     LTZero  LEZero  GTZero  GEZero  NotZero Top
    AnnotationMirror[][] neRefinements = {
            {lt0AM,   lt0AM,   lt0AM,  lt0AM,  lt0AM,  lt0AM,  lt0AM,  lt0AM,  lt0AM,  lt0AM,  lt0AM},  // LTZero != *
            {le0AM,   le0AM,   lt0AM,  le0AM,  le0AM,  le0AM,  le0AM,  le0AM,  le0AM,  le0AM,  le0AM},  // LEZero != *
            {gt0AM,   gt0AM,   gt0AM,  gt0AM,  gt0AM,  gt0AM,  gt0AM,  gt0AM,  gt0AM,  gt0AM,  gt0AM},  // GTZero != *
            {ge0AM,   ge0AM,   gt0AM,  ge0AM,  ge0AM,  ge0AM,  ge0AM,  ge0AM,  ge0AM,  ge0AM,  ge0AM},  // GEZero != *
            {not0AM,  not0AM,  not0AM, not0AM, not0AM, not0AM, not0AM, not0AM, not0AM, not0AM, not0AM}, // NotZero != *
            {top(),   top(),   not0AM, top(),  top(),  top(),  top(),  top(),  top(),  top(),  top()}   // Top != *
    };

    /**
     * Assuming that a simple comparison (lhs `op` rhs) returns true, this
     * function should refine what we know about the left-hand side (lhs). (The
     * input value "lhs" is always a legal return value, but not a very useful
     * one.)
     *
     * <p>For example, given the code
     * <pre>
     * if (y != 0) { x = 1 / y; }
     * </pre>
     * the comparison "y != 0" causes us to learn the fact that "y is not zero"
     * inside the body of the if-statement. This function would be called with
     * "NE", "top", and "zero", and should return "not zero" (or the appropriate
     * result for your lattice).
     *
     * <p>Note that the returned value should always be lower in the lattice
     * than the given point for lhs. The "glb" helper function below will
     * probably be useful here.
     *
     * @param operator   a comparison operator
     * @param lhs        the lattice point for the left-hand side of the comparison expression
     * @param rhs        the lattice point for the right-hand side of the comparison expression
     * @return a refined type for lhs
     */
    private AnnotationMirror refineLhsOfComparison(
            Comparison operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {

        /*System.out.println("--- refine ---");
        System.out.println(lhs.toString());
        System.out.println(rhs.toString());*/
        switch (operator) {
            case EQ:
                //System.out.println("--- eq ---");
                //System.out.println(glb(lhs, rhs));
                return glb(lhs, rhs);
            case NE:
                // System.out.println("--- ne ---");
                // System.out.println(refineWithRules(neRefinements, lhs, rhs));
                return refineWithRules(neRefinements, lhs, rhs);
            case LT:
                // System.out.println("--- lt ---");
                // System.out.println(refineWithRules(ltRefinements, lhs, rhs));
                return refineWithRules(ltRefinements, lhs, rhs);
            case LE:
                // System.out.println("--- le ---");
                // System.out.println(refineWithRules(leRefinements, lhs, rhs));
                return refineWithRules(leRefinements, lhs, rhs);
            case GT:
                // System.out.println("--- gt ---");
                // System.out.println(refineWithRules(gtRefinements, lhs, rhs));
                return refineWithRules(gtRefinements, lhs, rhs);
            case GE:
                // System.out.println("--- ge ---");
                // System.out.println(refineWithRules(geRefinements, lhs, rhs));
                return refineWithRules(geRefinements, lhs, rhs);
        }
        // TODO
        return lhs;
    }

    AnnotationMirror transferWithRules(AnnotationMirror[][] rules, AnnotationMirror lhs, AnnotationMirror rhs) {
        if (equal(lhs, bottom()) || equal(rhs, bottom())) {
            return bottom();
        }
        if (equal(lhs, top()) || equal(rhs, top())) {
            return top();
        }
        return rules[getIndexOfAnnotation(lhs)][getIndexOfAnnotation(rhs)];
    }

    AnnotationMirror transferDivideWithRules(AnnotationMirror[][] rules, AnnotationMirror lhs, AnnotationMirror rhs) {
        if (equal(lhs, bottom()) || equal(rhs, bottom())) {
            return bottom();
        }
        return rules[getIndexOfAnnotation(lhs)][getIndexOfAnnotation(rhs)];
    }

    //       MinusTwo    MinusOne    Zero        One         Two     LTZero LEZero GTZero GEZero NotZero
    AnnotationMirror[][] plusTransfers = {
            {lt0AM,      lt0AM,      minusTwoAM, minusOneAM, zeroAM, lt0AM, lt0AM, top(), top(), top()}, // MinusTwo + *
            {lt0AM,      minusTwoAM, minusOneAM, zeroAM,     oneAM,  lt0AM, lt0AM, ge0AM, top(), top()}, // MinusOne + *
            {minusTwoAM, minusOneAM, zeroAM,     oneAM,      twoAM,  lt0AM, le0AM, gt0AM, ge0AM, not0AM}, // Zero + *
            {minusOneAM, zeroAM,     oneAM,      twoAM,      gt0AM,  le0AM, top(), gt0AM, gt0AM, top()}, // One + *
            {zeroAM,     oneAM,      twoAM,      gt0AM,      gt0AM,  top(), top(), gt0AM, gt0AM, top()}, // Two + *
            {lt0AM,      lt0AM,      lt0AM,      le0AM,      top(),  lt0AM, lt0AM, top(), top(), top()}, // LTZero + *
            {lt0AM,      lt0AM,      le0AM,      top(),      top(),  lt0AM, le0AM, top(), top(), top()}, // LEZero + *
            {top(),      ge0AM,      gt0AM,      gt0AM,      gt0AM,  top(), top(), gt0AM, gt0AM, top()}, // GTZero + *
            {top(),      top(),      ge0AM,      gt0AM,      gt0AM,  top(), top(), gt0AM, ge0AM, top()}, // GEZero + *
            {top(),      top(),      not0AM,     top(),      top(),  top(), top(), top(), top(), top()}, // NotZero + *
    };

    //       MinusTwo    MinusOne    Zero    One         Two         LTZero  LEZero  GTZero  GEZero  NotZero
    AnnotationMirror[][] timesTransfers = {
            {gt0AM,      twoAM,      zeroAM, minusTwoAM, lt0AM,      gt0AM,  ge0AM,  lt0AM,  le0AM,  not0AM}, // MinusTwo * *
            {twoAM,      oneAM,      zeroAM, minusOneAM, minusTwoAM, gt0AM,  ge0AM,  lt0AM,  le0AM,  not0AM}, // MinusOne * *
            {zeroAM,     zeroAM,     zeroAM, zeroAM,     zeroAM,     zeroAM, zeroAM, zeroAM, zeroAM, zeroAM}, // Zero * *
            {minusTwoAM, minusOneAM, zeroAM, oneAM,      twoAM,      lt0AM,  le0AM,  gt0AM,  ge0AM,  not0AM}, // One * *
            {lt0AM,      minusTwoAM, zeroAM, twoAM,      gt0AM,      lt0AM,  le0AM,  gt0AM,  ge0AM,  not0AM}, // Two * *
            {gt0AM,      gt0AM,      zeroAM, lt0AM,      lt0AM,      gt0AM,  ge0AM,  lt0AM,  le0AM,  not0AM}, // LTZero * *
            {ge0AM,      ge0AM,      zeroAM, le0AM,      le0AM,      ge0AM,  ge0AM,  le0AM,  le0AM,  top()}, // LEZero * *
            {lt0AM,      lt0AM,      zeroAM, gt0AM,      gt0AM,      lt0AM,  le0AM,  gt0AM,  ge0AM,  not0AM}, // GTZero * *
            {le0AM,      le0AM,      zeroAM, ge0AM,      ge0AM,      le0AM,  le0AM,  ge0AM,  ge0AM,  top()}, // GEZero * *
            {not0AM,     not0AM,     zeroAM, not0AM,     not0AM,     not0AM, top(),  not0AM, top(),  not0AM}, // NotZero * *
    };
    //       MinusTwo    MinusOne    Zero      One         Two         LTZero  LEZero    GTZero  GEZero    NotZero Top
    AnnotationMirror[][] divideTransfers = {
            {oneAM,      twoAM,      bottom(), minusTwoAM, minusOneAM, ge0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // MinusTwo / *
            {zeroAM,     oneAM,      bottom(), minusOneAM, zeroAM,     ge0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // MinusOne / *
            {zeroAM,     zeroAM,     bottom(), zeroAM,     zeroAM,     zeroAM, bottom(), zeroAM, bottom(), zeroAM, bottom()}, // Zero / *
            {zeroAM,     minusOneAM, bottom(), oneAM,      zeroAM,     le0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // One / *
            {minusOneAM, minusTwoAM, bottom(), twoAM,      oneAM,      le0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // Two / *
            {ge0AM,      gt0AM,      bottom(), lt0AM,      le0AM,      ge0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // LTZero / *
            {ge0AM,      ge0AM,      bottom(), le0AM,      le0AM,      ge0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // LEZero / *
            {le0AM,      lt0AM,      bottom(), gt0AM,      ge0AM,      le0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // GTZero / *
            {le0AM,      le0AM,      bottom(), ge0AM,      ge0AM,      le0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // GEZero / *
            {top(),      not0AM,     bottom(), not0AM,     top(),      top(),  bottom(), top(),  bottom(), top(),  bottom()}, // NotZero / *
    };

    //       MinusTwo    MinusOne Zero      One     Two         LTZero  LEZero    GTZero  GEZero    NotZero Top
    AnnotationMirror[][] moduloTransfers = {
            {zeroAM,     zeroAM,  bottom(), zeroAM, zeroAM,     le0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // MinusTwo % *
            {minusOneAM, zeroAM,  bottom(), zeroAM, minusOneAM, le0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // MinusOne % *
            {zeroAM,     zeroAM,  bottom(), zeroAM, zeroAM,     zeroAM, bottom(), zeroAM, bottom(), top(),  bottom()}, // Zero % *
            {oneAM,      zeroAM,  bottom(), zeroAM, oneAM,      ge0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // One % *
            {zeroAM,     zeroAM,  bottom(), zeroAM, zeroAM,     ge0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // Two % *
            {le0AM,      zeroAM,  bottom(), zeroAM, le0AM,      le0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // LTZero % *
            {le0AM,      zeroAM,  bottom(), zeroAM, le0AM,      le0AM,  bottom(), le0AM,  bottom(), top(),  bottom()}, // LEZero % *
            {ge0AM,      zeroAM,  bottom(), zeroAM, ge0AM,      ge0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // GTZero % *
            {ge0AM,      zeroAM,  bottom(), zeroAM, ge0AM,      ge0AM,  bottom(), ge0AM,  bottom(), top(),  bottom()}, // GEZero % *
            {top(),      zeroAM,  bottom(), zeroAM, top(),      top(),  bottom(), top(),  bottom(), top(),  bottom()}, // NotZero / *
    };

    AnnotationMirror negateAnnotation(AnnotationMirror annotation) {
        ArrayList<Class<? extends Annotation>> negated = new ArrayList<>(Arrays.asList(
                Two.class,
                One.class,
                Zero.class,
                MinusOne.class,
                MinusTwo.class,
                GTZero.class,
                GEZero.class,
                LTZero.class,
                LEZero.class,
                NotZero.class,
                Top.class,
                Bottom.class));
        return reflect(negated.get(getIndexOfAnnotation(annotation)));
    }


    /**
     * For an arithmetic expression (lhs `op` rhs), compute the point in the
     * lattice for the result of evaluating the expression. ("Top" is always a
     * legal return value, but not a very useful one.)
     *
     * <p>For example,
     * <pre>x = 1 + 0</pre>
     * should cause us to conclude that "x is not zero".
     *
     * @param operator   a binary operator
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
     * @return the lattice point for the result of the expression
     */
    private AnnotationMirror arithmeticTransfer(
            BinaryOperator operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        // TODO
        // System.out.println("--- arith ---");
        // System.out.println(operator);
        // System.out.println(lhs);
        // System.out.println(rhs);
        switch (operator) {
            case PLUS:
                // System.out.println(transferWithRules(plusTransfers, lhs, rhs));
                return transferWithRules(plusTransfers, lhs, rhs);
            case MINUS:
                // System.out.println(transferWithRules(plusTransfers, lhs, negateAnnotation(rhs)));
                return transferWithRules(plusTransfers, lhs, negateAnnotation(rhs));
            case TIMES:
                // System.out.println(transferWithRules(timesTransfers, lhs, rhs));
                return transferWithRules(timesTransfers, lhs, rhs);
            case DIVIDE:
                // System.out.println(transferWithRules(divideTransfers, lhs, rhs));
                return transferWithRules(divideTransfers, lhs, rhs);
            case MOD:
                // System.out.println(transferWithRules(moduloTransfers, lhs, rhs));
                return transferWithRules(moduloTransfers, lhs, rhs);
        }
        return top();
    }

    // ========================================================================
    // Useful helpers

    /** Get the top of the lattice */
    private AnnotationMirror top() {
        return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
    }

    /** Get the bottom of the lattice */
    private AnnotationMirror bottom() {
        return analysis.getTypeFactory().getQualifierHierarchy().getBottomAnnotations().iterator().next();
    }

    /** Compute the least-upper-bound of two points in the lattice */
    private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBound(x, y);
    }

    /** Compute the greatest-lower-bound of two points in the lattice */
    private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBound(x, y);
    }

    /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
    private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
        return AnnotationBuilder.fromClass(
            analysis.getTypeFactory().getProcessingEnv().getElementUtils(),
            qualifier);
    }

    /** Determine whether two AnnotationMirrors are the same point in the lattice */
    private boolean equal(AnnotationMirror x, AnnotationMirror y) {
        return AnnotationUtils.areSame(x, y);
    }

    /** `x op y` == `y flip(op) x` */
    private Comparison flip(Comparison op) {
        switch (op) {
            case EQ: return Comparison.EQ;
            case NE: return Comparison.NE;
            case LT: return Comparison.GT;
            case LE: return Comparison.GE;
            case GT: return Comparison.LT;
            case GE: return Comparison.LE;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    /** `x op y` == `!(x negate(op) y)` */
    private Comparison negate(Comparison op) {
        switch (op) {
            case EQ: return Comparison.NE;
            case NE: return Comparison.EQ;
            case LT: return Comparison.GE;
            case LE: return Comparison.GT;
            case GT: return Comparison.LE;
            case GE: return Comparison.LT;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroTransfer(CFAnalysis analysis) {
        super(analysis);
    }

    private TransferResult<CFValue, CFStore> implementComparison(Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        CFStore thenStore = out.getThenStore().copy();
        CFStore elseStore = out.getElseStore().copy();

        thenStore.insertValue(
                JavaExpression.fromNode(n.getLeftOperand()),
            refineLhsOfComparison(op, l, r));

        thenStore.insertValue(
            JavaExpression.fromNode(n.getRightOperand()),
            refineLhsOfComparison(flip(op), r, l));

        elseStore.insertValue(
            JavaExpression.fromNode(n.getLeftOperand()),
            refineLhsOfComparison(negate(op), l, r));

        elseStore.insertValue(
            JavaExpression.fromNode(n.getRightOperand()),
            refineLhsOfComparison(flip(negate(op)), r, l));

        // System.out.println("--- if ---");
        // System.out.println(thenStore);
        // System.out.println(elseStore);

        return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
    }

    private TransferResult<CFValue, CFStore> implementOperator(BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        AnnotationMirror res = arithmeticTransfer(op, l, r);
        CFValue newResultValue = analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
        return new RegularTransferResult<>(newResultValue, out.getRegularStore());
    }

    @Override
    public TransferResult<CFValue, CFStore> visitEqualTo(EqualToNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNotEqual(NotEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThan(GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThan(LessThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThanOrEqual(LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerDivision(IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerRemainder(IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingDivision(FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingRemainder(FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalMultiplication(NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalAddition(NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalSubtraction(NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MINUS, n, super.visitNumericalSubtraction(n, p));
    }

    private static AnnotationMirror findAnnotation(
            Set<AnnotationMirror> set, QualifierHierarchy hierarchy) {
        if (set.size() == 0) {
            return null;
        }
        Set<? extends AnnotationMirror> tops = hierarchy.getTopAnnotations();
        return hierarchy.findAnnotationInSameHierarchy(set, tops.iterator().next());
    }

}
