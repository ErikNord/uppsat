(set-info :status unknown)
(set-info :source |Alberto Griggio <griggio@fbk.eu>. These benchmarks were used for the evaluation in the following paper: L. Haller, A. Griggio, M. Brain, D. Kroening: Deciding floating-point logic with systematic abstraction. FMCAD 2012.)|)
(set-logic QF_FPBV)
(declare-fun b37 () (_ FloatingPoint 8 24))
(declare-fun b20 () (_ FloatingPoint 11 53))
(declare-fun b11 () (_ FloatingPoint 8 24))
(declare-fun b13 () (_ FloatingPoint 8 24))
(declare-fun b16 () (_ FloatingPoint 8 24))
(declare-fun b34 () (_ FloatingPoint 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FloatingPoint 8 24) b34)
(define-fun .10 () (_ FloatingPoint 8 24) b11)
(define-fun .11 () Bool (fp.lt .9 .10))
(define-fun .12 () (_ FloatingPoint 8 24) b13)
(define-fun .13 () (_ FloatingPoint 8 24) (fp.mul .3 .10 .12))
(define-fun .14 () (_ FloatingPoint 8 24) b16)
(define-fun .15 () (_ FloatingPoint 8 24) (fp.mul .3 .13 .14))
(define-fun .16 () (_ FloatingPoint 11 53) ((_ to_fp 11 53) .3 .15))
(define-fun .17 () (_ FloatingPoint 11 53) b20)
(define-fun .18 () Bool (fp.lt .17 .16))
(define-fun .19 () Bool (and .11 .18))
(define-fun .20 () (_ FloatingPoint 8 24) b37)
(define-fun .21 () Bool (fp.lt .10 .20))
(define-fun .22 () Bool (and .19 .21))
(define-fun .23 () Bool (fp.lt .9 .12))
(define-fun .24 () Bool (and .22 .23))
(define-fun .25 () Bool (fp.lt .12 .20))
(define-fun .26 () Bool (and .24 .25))
(define-fun .27 () Bool (fp.lt .9 .14))
(define-fun .28 () Bool (and .26 .27))
(define-fun .29 () Bool (fp.lt .14 .20))
(define-fun .30 () Bool (and .28 .29))
(assert .30)
(check-sat)