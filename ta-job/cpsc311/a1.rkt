#lang plai
(print-only-errors)
(define (... . args) (cons '... args)) ;; enables us to use ... in templates

;; CPSC311 2023 Winter Term 1
;; Assignment 0: Designing Functions over Trees using PLAI data types

;; Released: Tuesday, September 12, 2023
;; Due: Sunday, September 17, 2023 at 11:59pm

;; This assignment is to be completed individually
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Name:
;; Student Number:
;; CWL:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 2htdp/image)

;;
;; Render Tree and Me
;;

;; A render tree lets you arrange images relative to one another.

(define-type render-tree
  [img (i image?)]
  [vertical (rt* (listof render-tree?))]
  [horizontal (rt1 render-tree?) (rt2 render-tree?)])
;; interp.
;; layout instructions for a collection of images:
;; - (img i) is the image i
;; - (vertical rt*) renders the list of render-trees vertically,
;;   with the first image in the list above the last.  An empty list
;;   renders as the empty-image
;; - (horizontal rt1 rt2) renders rt1 to the left of rt2

(define RT0 (img (square 20 "solid" "red")))
(define RT1 (img (square 20 "solid" "blue")))
(define RT2 (horizontal RT0 (horizontal RT1 RT0)))
(define RT3 (horizontal RT1
                        (horizontal RT0
                                    (horizontal RT1
                                                (img empty-image)))))
(define RT4 (vertical (list RT2 RT3 RT2)))
(define RT5 (horizontal (img empty-image) (img empty-image)))
(define RT6 (vertical (list)))

;; CPSC110 BSL-Style Template (for reference, NOT FOR USE)
#;
(define (fn-for-rt rt)
  (cond [(img? rt) (... (img-i rt))]
        [(vertical? rt)
         (... (fn-for-lort (vertical-rt* rt)))]
        [else ; (horizontal? rt)
         (... (fn-for-rt (horizontal-rt1 rt))
              (fn-for-rt (horizontal-rt2 rt)))]))


;; CPSC311 PLAI-Style Template (USE THIS ONE)
#;
(define (fn-for-rt rt)
  (type-case render-tree rt
    [img (i) (... i)]
    [vertical (rt*) (... (fn-for-lort rt*))]
    [horizontal (rt1 rt2) (... (fn-for-rt rt1)
                               (fn-for-rt rt2))]))

;; structurally recursive list of render-tree template
#;
(define (fn-for-lort lort)
  (cond [(empty? lort) (...)]
        [else ; (cons? lort)]
         (... (fn-for-rt (first lort))
              (fn-for-lort (rest lort)))]))

;; example abstract function list of render-tree template
#;
(define (fn-for-lort2 lort)
  (foldr ... ...
         (map ... lort)))


;; For the following problems, you are expected to follow the design recipes.
;; See https://www.students.cs.ubc.ca/~cs-311/current/syllabus.html#coding-style
;; and #examples.

;; Use the PLAI-Style render-tree template where appropriate, and either
;; the structurally recursive list template or a template that uses
;; abstract list functions, if you prefer.

;; DO NOT use encapsulation (i.e. local) for this assignment.  Encapsulation
;; will be allowed in future assignments.

;; Problem 1: Ho Ho Ho (in September?!?)
;; Whoever designed the render-tree data structure can't seem to decide between
;; elegant generality and spartan simplicity: vertical takes a list of
;; any number of render trees, but horizontal takes exactly two.
;; But it would be nice if both could behave the same.  With a little
;; effort, we can build a more uniform interface to the data type.

;; Design a function, called horizontal* that accepts an
;; list of render-trees and produces a render-tree that
;; lays them out from left-to-right.  HINT: empty-image is your friend.

;; (listof RenderTree) -> RenderTree
;; produce a render tree that horizontally renders of the given render trees
(define (horizontal* lort) (img empty-image)) ; stub



;; Problem 2: Paint Me A Picture
;; Design a function called render that renders the given render tree
;; as an image.  You will want to use the built-in above and beside functions.
;; Fix the signature and purpose of render/lort by replacing ??? with
;; the appropriate return type and purpose.

;; RenderTree -> Image
;; (listof RenderTree) -> ???
;; produce the proper rendering of the given render tree
;; produce ???
(define (render rt) empty-image) ; stub
(define (render/lort lort) (...)) ; partial stub



;; Problem 3: Put the Render in the Blender
;; Sometimes, don't you just want to SHAKE THINGS UP?!?
;; Design a function called blend that, given a render tree, produces a new
;; render tree that horizontally renders all render trees that were vertically
;; rendered originally, and vertically renders all render trees
;; that were horizontally rendered originally.
;; Fix the signature and purpose of the blend/lort by replacing ??? with
;; the appropriate return type and purpose.
;; HINT: be mindful of the work you have already done.

;; RenderTree -> RenderTree
;; (listof RenderTree) -> ???
;; produce a render tree that swaps all horizontal and vertical renderings
;; produce ???
(define (blend rt) (img empty-image)) ; stub
(define (blend/lort lort) (...)) ; partial stub,
