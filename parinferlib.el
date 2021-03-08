;;; parinferlib.el --- A Parinfer implementation in Emacs Lisp
;;
;; Author: Chris Oakman
;; Homepage: https://github.com/oakmac/parinfer-elisp
;; Version: 1.0.0
;; Package-Requires: ((emacs "24.3"))
;; Keywords: parinfer, extensions
;;
;;; Commentary:
;;
;; Kisaragi Hiu: I'm modifying this in hope of making it more
;; performant, as well as make it more idiomatic.
;;
;;; Original commentary:
;;
;; More information about Parinfer can be found here:
;; http://shaunlebron.github.io/parinfer/
;;
;; Copyright (c) 2016, Chris Oakman
;; Released under the ISC license
;; https://github.com/oakmac/parinfer-elisp/blob/master/LICENSE.md

;; NOTE: everything is namespaced under `parinferlib` with the assumption that
;;       Emacs extensions might use `parinfer`

;;; Code:

;;------------------------------------------------------------------------------
;; Constants / Predicates
;;------------------------------------------------------------------------------

(defconst parinferlib--BACKSLASH "\\")
(defconst parinferlib--BLANK_SPACE " ")
(defconst parinferlib--DOUBLE_SPACE "  ")
(defconst parinferlib--DOUBLE_QUOTE "\"")
(defconst parinferlib--NEWLINE "\n")
(defconst parinferlib--LINE_ENDING_REGEX "\r?\n")
(defconst parinferlib--SEMICOLON ";")
(defconst parinferlib--TAB "\t")

;; A Stack Element is a Vector of 4 items (alphabetically ordered)
;; idx : item
;;   0 : ch
;;   1 : indentDelta
;;   2 : lineNo
;;   3 : x
;; A Stack Element has four fields:
;; - ch
;; - indent-delta
;; - line-no
;; - x

(defsubst parinferlib--stack-elem (ch indent-delta line-no x)
  "Create a Stack Element.
A Stack Element has four fields: CH, INDENT-DELTA, LINE-NO, and X."
  (declare (side-effect-free t))
  (vector ch indent-delta line-no x))
(defsubst parinferlib--stack-elem-ch (elem)
  "Access slot \"ch\" of `parinferlib--stack-elem' struct ELEM."
  (declare (side-effect-free t))
  (aref elem 0))
(defsubst parinferlib--stack-elem-indent-delta (elem)
  "Access slot \"indent-delta\" of `parinferlib--stack-elem' struct ELEM."
  (declare (side-effect-free t))
  (aref elem 1))
(defsubst parinferlib--stack-elem-line-no (elem)
  "Access slot \"line-no\" of `parinferlib--stack-elem' struct ELEM."
  (declare (side-effect-free t))
  (aref elem 2))
(defsubst parinferlib--stack-elem-x (elem)
  "Access slot \"x\" of `parinferlib--stack-elem' struct ELEM."
  (declare (side-effect-free t))
  (aref elem 3))

;; determines if a line only contains a Paren Trail (possibly w/ a comment)
(defconst parinferlib--STANDALONE_PAREN_TRAIL "^[][:space:])}]*\\(;.*\\)?$")

(defconst parinferlib--PARENS (make-hash-table :test 'equal))
(puthash "{" "}" parinferlib--PARENS)
(puthash "}" "{" parinferlib--PARENS)
(puthash "[" "]" parinferlib--PARENS)
(puthash "]" "[" parinferlib--PARENS)
(puthash "(" ")" parinferlib--PARENS)
(puthash ")" "(" parinferlib--PARENS)

(defun parinferlib--open-paren? (ch)
  "Is CH an open paren?"
  (member ch '("(" "{" "[")))

(defun parinferlib--close-paren? (ch)
  "Is CH a close paren?"
  (member ch '(")" "}" "]")))

;;------------------------------------------------------------------------------
;; Result Structure
;;------------------------------------------------------------------------------

(defvar-local parinferlib--result nil
  "Current parsing result.")

(defun parinferlib--create-initial-result (text mode options)
  "Initialize the result object."
  (let ((lines-vector (vconcat (split-string text parinferlib--LINE_ENDING_REGEX)))
        (result (make-hash-table)))
    (puthash :mode mode result)

    (puthash :origText text result)
    (puthash :origLines lines-vector result)
    (puthash :origCursorX nil result)

    (puthash :lines (make-vector (length lines-vector) nil) result)
    (puthash :lineNo -1 result)
    (puthash :ch "" result)
    (puthash :x 0 result)

    (puthash :parenStack '() result)
    (puthash :tabStops '() result)

    (puthash :parenTrailLineNo nil result)
    (puthash :parenTrailStartX nil result)
    (puthash :parenTrailEndX nil result)
    (puthash :parenTrailOpeners '() result)

    (puthash :cursorX nil result)
    (puthash :cursorLine nil result)
    (puthash :cursorDx nil result)
    (puthash :previewCursorScope nil result)
    (puthash :canPreviewCursorScope nil result)

    (puthash :isInCode t result)
    (puthash :isEscaping nil result)
    (puthash :isInStr nil result)
    (puthash :isInComment nil result)
    (puthash :commentX nil result)

    (puthash :quoteDanger nil result)
    (puthash :trackingIndent nil result)
    (puthash :skipChar nil result)
    (puthash :success nil result)

    (puthash :maxIndent nil result)
    (puthash :indentDelta 0 result)

    (puthash :error nil result)

    ;; a plist of potential error positions
    (puthash :errorPosCache '() result)

    ;; merge options if they are valid
    (when (integerp (plist-get options :cursor-x))
      (puthash :cursorX (plist-get options :cursor-x) result)
      (puthash :origCursorX (plist-get options :cursor-x) result))
    (when (integerp (plist-get options :cursor-line))
      (puthash :cursorLine (plist-get options :cursor-line) result))
    (when (integerp (plist-get options :cursor-dx))
      (puthash :cursorDx (plist-get options :cursor-dx) result))
    (when (booleanp (plist-get options :preview-cursor-scope))
      (puthash :previewCursorScope (plist-get options :preview-cursor-scope) result))

    (setq parinferlib--result result)))

;;------------------------------------------------------------------------------
;; Errors
;;------------------------------------------------------------------------------

(defconst parinferlib--err-messages
  '((quote-danger . "Quotes must balanced inside comment blocks.")
    (eol-backslash . "Line cannot end in a hanging backslash.")
    (unclosed-quote . "String is missing a closing quote.")
    (unclosed-paren . "Unmatched open-paren."))
  "Alist mapping error symbols to error messages.")

(defun parinferlib--cache-error-pos (error-name line-no x)
  (let* ((error-cache (gethash :errorPosCache parinferlib--result))
         (position (list :line-no line-no :x x))
         (updated-error-cache (plist-put error-cache error-name position)))
    (puthash :errorPosCache updated-error-cache parinferlib--result)))

(defun parinferlib--create-error (error line-no x)
  "Create an error object.

RESULT: the current result.
ERROR: one of the keys in `parinferlib--err-messages'.
LINE-NO: current line number.
X: current position."
  (let* ((error-cache (gethash :errorPosCache parinferlib--result))
         (error-msg (cdr (assq error parinferlib--err-messages)))
         (error-position (plist-get error-cache error)))
    (when (not line-no)
      (setq line-no (plist-get error-position :line-no)))
    (when (not x)
      (setq x (plist-get error-position :x)))

    ;; return a plist of the error
    (list :name (symbol-name error)
          :message error-msg
          :line-no line-no
          :x x)))

;;------------------------------------------------------------------------------
;; String Operations
;;------------------------------------------------------------------------------

(defun parinferlib--replace-within-string (orig start end replace)
  (let* ((orig-length (length orig))
         (head (substring orig 0 start))
         (tail (if (>= end orig-length)
                 ""
                 (substring orig end))))
    (concat head replace tail)))

;;------------------------------------------------------------------------------
;; Line Operations
;;------------------------------------------------------------------------------

(defun parinferlib--cursor-affected? (start end)
  (let ((cursor-x (gethash :cursorX parinferlib--result)))
    (if (and (equal cursor-x start)
             (equal cursor-x end))
        (zerop cursor-x)
      (>= cursor-x end))))

(defun parinferlib--shift-cursor-on-edit (line-no start end replace)
  (let* ((old-length (- end start))
         (new-length (length replace))
         (dx (- new-length old-length))
         (cursor-line (gethash :cursorLine parinferlib--result))
         (cursor-x (gethash :cursorX parinferlib--result)))
    (when (and dx
               (not (zerop dx))
               (equal cursor-line line-no)
               cursor-x
               (parinferlib--cursor-affected? start end))
      (puthash :cursorX (+ cursor-x dx) parinferlib--result))))

(defun parinferlib--replace-within-line (line-no start end replace)
  (let* ((lines (gethash :lines parinferlib--result))
         (line (aref lines line-no))
         (new-line (parinferlib--replace-within-string line start end replace)))
    (aset lines line-no new-line)
    (parinferlib--shift-cursor-on-edit line-no start end replace)))

(defun parinferlib--insert-within-line (line-no idx insert)
  (parinferlib--replace-within-line line-no idx idx insert))

(defun parinferlib--init-line (line)
  (let* ((current-line-no (gethash :lineNo parinferlib--result))
         (new-line-no (1+ current-line-no))
         (lines (gethash :lines parinferlib--result)))
    (aset lines new-line-no line)

    (puthash :x 0 parinferlib--result)
    (puthash :lineNo new-line-no parinferlib--result)

    ;; reset line-specific state
    (puthash :commentX nil parinferlib--result)
    (puthash :indentDelta 0 parinferlib--result)))

;; if the current character has changed, commit it's change to the current line
(defun parinferlib--commit-char (orig-ch)
  (let* ((line-no (gethash :lineNo parinferlib--result))
         (x (gethash :x parinferlib--result))
         (ch (gethash :ch parinferlib--result))
         (ch-length (length ch))
         (orig-ch-length (length orig-ch)))
    (when (not (string= orig-ch ch))
      (parinferlib--replace-within-line line-no x (+ x orig-ch-length) ch))
    (puthash :x (+ x ch-length) parinferlib--result)))

;;------------------------------------------------------------------------------
;; Util
;;------------------------------------------------------------------------------

(defun parinferlib--clamp (val-n min-n max-n)
  (when min-n
    (setq val-n (if (> min-n val-n) min-n val-n)))
  (when max-n
    (setq val-n (if (< max-n val-n) max-n val-n)))
  val-n)

;;------------------------------------------------------------------------------
;; Character functions
;;------------------------------------------------------------------------------

(defun parinferlib--valid-close-paren? (paren-stack ch)
  (when paren-stack
    (let* ((top-of-stack (car paren-stack))
           (top-of-stack-ch (parinferlib--stack-elem-ch top-of-stack)))
      (string= top-of-stack-ch (gethash ch parinferlib--PARENS)))))

(defun parinferlib--on-open-paren ()
  (when (gethash :isInCode parinferlib--result)
    (let* ((new-stack-el (parinferlib--stack-elem
                          (gethash :ch parinferlib--result)
                          (gethash :indentDelta parinferlib--result)
                          (gethash :lineNo parinferlib--result)
                          (gethash :x parinferlib--result)))
           (paren-stack (gethash :parenStack parinferlib--result))
           (new-paren-stack (cons new-stack-el paren-stack)))
      (puthash :parenStack new-paren-stack parinferlib--result))))

(defun parinferlib--on-matched-close-paren ()
  (let* ((paren-stack (gethash :parenStack parinferlib--result))
         (opener (pop paren-stack))
         (opener-x (parinferlib--stack-elem-x opener))
         (result-x (gethash :x parinferlib--result))
         (openers (gethash :parenTrailOpeners parinferlib--result))
         (new-openers (cons opener openers)))
    (puthash :parenTrailEndX (1+ result-x) parinferlib--result)
    (puthash :parenTrailOpeners new-openers parinferlib--result)
    (puthash :maxIndent opener-x parinferlib--result)
    ;; the first element of paren-stack was removed when we called "pop" earlier
    (puthash :parenStack paren-stack parinferlib--result)))

(defun parinferlib--on-unmatched-close-paren ()
  (puthash :ch "" parinferlib--result))

(defun parinferlib--on-close-paren ()
  (when (gethash :isInCode parinferlib--result)
    (if (parinferlib--valid-close-paren? (gethash :parenStack parinferlib--result) (gethash :ch parinferlib--result))
      (parinferlib--on-matched-close-paren)
      (parinferlib--on-unmatched-close-paren))))

(defun parinferlib--on-tab ()
  (when (gethash :isInCode parinferlib--result)
    (puthash :ch parinferlib--DOUBLE_SPACE parinferlib--result)))

(defun parinferlib--on-semicolon ()
  (when (gethash :isInCode parinferlib--result)
    (puthash :isInComment t parinferlib--result)
    (puthash :commentX (gethash :x parinferlib--result) parinferlib--result)))

(defun parinferlib--on-newline ()
  (puthash :isInComment nil parinferlib--result)
  (puthash :ch "" parinferlib--result))

(defun parinferlib--on-quote ()
  (cond ((gethash :isInStr parinferlib--result)
         (puthash :isInStr nil parinferlib--result))

        ((gethash :isInComment parinferlib--result)
         (let ((quote-danger (gethash :quoteDanger parinferlib--result)))
           (puthash :quoteDanger (not quote-danger) parinferlib--result)
           (when (gethash :quoteDanger parinferlib--result)
             (let ((line-no (gethash :lineNo parinferlib--result))
                   (x (gethash :x parinferlib--result)))
               (parinferlib--cache-error-pos 'quote-danger line-no x)))))

        (t
         (let ((line-no (gethash :lineNo parinferlib--result))
               (x (gethash :x parinferlib--result)))
           (puthash :isInStr t parinferlib--result)
           (parinferlib--cache-error-pos 'unclosed-quote line-no x)))))

(defun parinferlib--on-backslash ()
  (puthash :isEscaping t parinferlib--result))

(defun parinferlib--after-backslash ()
  (puthash :isEscaping nil parinferlib--result)
  (when (string= (gethash :ch parinferlib--result) parinferlib--NEWLINE)
    (when (gethash :isInCode parinferlib--result)
      (let ((line-no (gethash :lineNo parinferlib--result))
            (x (gethash :x parinferlib--result)))
        (throw 'parinferlib-error (parinferlib--create-error 'eol-backslash line-no (1- x)))))
    (parinferlib--on-newline)))

(defun parinferlib--on-char ()
  (let ((ch (gethash :ch parinferlib--result)))
    (cond ((gethash :isEscaping parinferlib--result)   (parinferlib--after-backslash))
          ((parinferlib--open-paren? ch)  (parinferlib--on-open-paren))
          ((parinferlib--close-paren? ch) (parinferlib--on-close-paren))
          ((string= ch parinferlib--DOUBLE_QUOTE) (parinferlib--on-quote))
          ((string= ch parinferlib--SEMICOLON)    (parinferlib--on-semicolon))
          ((string= ch parinferlib--BACKSLASH)    (parinferlib--on-backslash))
          ((string= ch parinferlib--TAB)          (parinferlib--on-tab))
          ((string= ch parinferlib--NEWLINE)      (parinferlib--on-newline))))
  (let ((in-comment? (gethash :isInComment parinferlib--result))
        (in-string? (gethash :isInStr parinferlib--result)))
    (puthash :isInCode (and (not in-comment?) (not in-string?)) parinferlib--result)))

;;------------------------------------------------------------------------------
;; Cursor functions
;;------------------------------------------------------------------------------

(defun parinferlib--cursor-on-left? ()
  (let* ((line-no (gethash :lineNo parinferlib--result))
         (cursor-line (gethash :cursorLine parinferlib--result))
         (cursor-x (gethash :cursorX parinferlib--result))
         (result-x (gethash :x parinferlib--result)))
    (and (equal line-no cursor-line)
         cursor-x
         result-x
         (<= cursor-x result-x))))

(defun parinferlib--cursor-on-right? (x)
  (let* ((line-no (gethash :lineNo parinferlib--result))
         (cursor-line (gethash :cursorLine parinferlib--result))
         (cursor-x (gethash :cursorX parinferlib--result)))
    (and (equal line-no cursor-line)
         cursor-x
         x
         (> cursor-x x))))

(defun parinferlib--cursor-in-comment? ()
  (parinferlib--cursor-on-right? (gethash :commentX parinferlib--result)))

(defun parinferlib--handle-cursor-delta ()
  (let* ((cursor-dx (gethash :cursorDx parinferlib--result))
         (cursor-line (gethash :cursorLine parinferlib--result))
         (line-no (gethash :lineNo parinferlib--result))
         (cursor-x (gethash :cursorX parinferlib--result))
         (x (gethash :x parinferlib--result))
         (indent-delta (gethash :indentDelta parinferlib--result))
         (has-delta? (and cursor-dx
                          (equal cursor-line line-no)
                          (equal cursor-x x))))
    (when has-delta?
      (puthash :indentDelta (+ indent-delta cursor-dx) parinferlib--result))))

;;------------------------------------------------------------------------------
;; Paren Trail functions
;;------------------------------------------------------------------------------

(defun parinferlib--reset-paren-trail (line-no x)
  (puthash :parenTrailLineNo line-no parinferlib--result)
  (puthash :parenTrailStartX x parinferlib--result)
  (puthash :parenTrailEndX x parinferlib--result)
  (puthash :parenTrailOpeners '() parinferlib--result)
  (puthash :maxIndent nil parinferlib--result))

(defun parinferlib--update-paren-trail-bounds ()
  (let* ((lines (gethash :lines parinferlib--result))
         (line-no (gethash :lineNo parinferlib--result))
         (line (aref lines line-no))
         (x (gethash :x parinferlib--result))
         (prev-ch (if (> x 0)
                    (string (aref line (1- x)))
                    nil))
         (ch (gethash :ch parinferlib--result))
         (should-reset? (and (gethash :isInCode parinferlib--result)
                             (or (not (parinferlib--close-paren? ch))
                                 (string= prev-ch parinferlib--BACKSLASH))
                             (not (string= ch ""))
                             (or (not (string= ch parinferlib--BLANK_SPACE))
                                 (string= prev-ch parinferlib--BACKSLASH))
                             (not (string= ch parinferlib--DOUBLE_SPACE)))))
    (when should-reset?
      (parinferlib--reset-paren-trail line-no (1+ x)))))

(defun parinferlib--clamp-paren-trail-to-cursor ()
  (let* ((start-x (gethash :parenTrailStartX parinferlib--result))
         (end-x (gethash :parenTrailEndX parinferlib--result))
         (cursor-clamping? (and (parinferlib--cursor-on-right? start-x)
                                (not (parinferlib--cursor-in-comment?)))))
    (when cursor-clamping?
      (let* ((cursor-x (gethash :cursorX parinferlib--result))
             (new-start-x (max start-x cursor-x))
             (new-end-x (max end-x cursor-x))
             (line-no (gethash :lineNo parinferlib--result))
             (lines (gethash :lines parinferlib--result))
             (line (aref lines line-no))
             (remove-count 0)
             (i start-x))
        (while (< i new-start-x)
          (when (parinferlib--close-paren? (string (aref line i)))
            (setq remove-count (1+ remove-count)))
          (setq i (1+ i)))
        (when (> remove-count 0)
          (let* ((openers (gethash :parenTrailOpeners parinferlib--result))
                 (new-openers (nbutlast openers remove-count)))
            (puthash :parenTrailOpeners new-openers parinferlib--result)))
        (puthash :parenTrailStartX new-start-x parinferlib--result)
        (puthash :parenTrailEndX new-end-x parinferlib--result)))))

(defun parinferlib--pop-paren-trail ()
  (let ((start-x (gethash :parenTrailStartX parinferlib--result))
        (end-x (gethash :parenTrailEndX parinferlib--result)))
    (when (not (equal start-x end-x))
      (let ((openers (gethash :parenTrailOpeners parinferlib--result))
            (paren-stack (gethash :parenStack parinferlib--result)))
        (while openers
          (setq paren-stack (cons (pop openers) paren-stack)))
        (puthash :parenTrailOpeners openers parinferlib--result)
        (puthash :parenStack paren-stack parinferlib--result)))))

(defun parinferlib--correct-paren-trail (indent-x)
  (let ((parens "")
        (paren-stack (gethash :parenStack parinferlib--result))
        (break? nil))
    (while (and (> (length paren-stack) 0)
                (not break?))
      (let* ((opener (car paren-stack))
             (opener-x (parinferlib--stack-elem-x opener))
             (opener-ch (parinferlib--stack-elem-ch opener)))
        (if (>= opener-x indent-x)
          (progn (pop paren-stack)
                 (setq parens (concat parens (gethash opener-ch parinferlib--PARENS))))
          (setq break? t))))
    (puthash :parenStack paren-stack parinferlib--result)
    (let ((paren-trail-line-no (gethash :parenTrailLineNo parinferlib--result))
          (paren-trail-start-x (gethash :parenTrailStartX parinferlib--result))
          (paren-trail-end-x (gethash :parenTrailEndX parinferlib--result)))
      (parinferlib--replace-within-line paren-trail-line-no paren-trail-start-x paren-trail-end-x parens))))

(defun parinferlib--clean-paren-trail ()
  (let* ((start-x (gethash :parenTrailStartX parinferlib--result))
         (end-x (gethash :parenTrailEndX parinferlib--result))
         (line-no (gethash :lineNo parinferlib--result))
         (paren-trail-line-no (gethash :parenTrailLineNo parinferlib--result))
         (exit-early? (or (equal start-x end-x)
                          (not (equal line-no paren-trail-line-no)))))
    (when (not exit-early?)
      (let* ((lines (gethash :lines parinferlib--result))
             (line (aref lines line-no))
             (new-trail "")
             (space-count 0)
             (i start-x))
        (while (< i end-x)
          (let ((ch (string (aref line i))))
            (if (parinferlib--close-paren? ch)
              (setq new-trail (concat new-trail ch))
              (setq space-count (1+ space-count))))
          (setq i (1+ i)))
        (when (> space-count 0)
          (parinferlib--replace-within-line line-no start-x end-x new-trail)
          (let* ((paren-trail-end-x (gethash :parenTrailEndX parinferlib--result))
                 (new-pt-end-x (- paren-trail-end-x space-count)))
            (puthash :parenTrailEndX new-pt-end-x parinferlib--result)))))))

(defun parinferlib--append-paren-trail ()
  (let* ((paren-stack (gethash :parenStack parinferlib--result))
         (opener (pop paren-stack))
         (opener-ch (parinferlib--stack-elem-ch opener))
         (opener-x (parinferlib--stack-elem-x opener))
         (close-ch (gethash opener-ch parinferlib--PARENS))
         (paren-trail-line-no (gethash :parenTrailLineNo parinferlib--result))
         (end-x (gethash :parenTrailEndX parinferlib--result)))
    (puthash :parenStack paren-stack parinferlib--result)
    (puthash :maxIndent opener-x parinferlib--result)
    (parinferlib--insert-within-line paren-trail-line-no end-x close-ch)
    (puthash :parenTrailEndX (1+ end-x) parinferlib--result)))

(defun parinferlib--invalidate-paren-trail ()
  (puthash :parenTrailLineNo nil parinferlib--result)
  (puthash :parenTrailStartX nil parinferlib--result)
  (puthash :parenTrailEndX nil parinferlib--result)
  (puthash :parenTrailOpeners '() parinferlib--result))

(defun parinferlib--finish-new-paren-trail ()
  (let* ((in-str? (gethash :isInStr parinferlib--result))
         (mode (gethash :mode parinferlib--result))
         (line-no (gethash :lineNo parinferlib--result))
         (cursor-line (gethash :cursorLine parinferlib--result)))
    (cond
      (in-str?
       (parinferlib--invalidate-paren-trail))

      ((equal mode :indent)
       (progn
         (parinferlib--clamp-paren-trail-to-cursor)
         (parinferlib--pop-paren-trail)))


      ((and (equal mode :paren)
            (not (equal line-no cursor-line)))
       (parinferlib--clean-paren-trail)))))

;;------------------------------------------------------------------------------
;; Indentation functions
;;------------------------------------------------------------------------------

(defun parinferlib--correct-indent ()
  (let* ((orig-indent (gethash :x parinferlib--result))
         (new-indent orig-indent)
         (min-indent 0)
         (max-indent (gethash :maxIndent parinferlib--result))
         (paren-stack (gethash :parenStack parinferlib--result))
         (opener (car paren-stack)))
    (when opener
      (let* ((opener-x (parinferlib--stack-elem-x opener))
             (opener-indent-delta (parinferlib--stack-elem-indent-delta opener)))
        (setq min-indent (1+ opener-x))
        (setq new-indent (+ new-indent opener-indent-delta))))
    (setq new-indent (parinferlib--clamp new-indent min-indent max-indent))
    (when (not (equal new-indent orig-indent))
      (let* ((indent-str (make-string new-indent (aref parinferlib--BLANK_SPACE 0)))
             (line-no (gethash :lineNo parinferlib--result))
             (indent-delta (gethash :indentDelta parinferlib--result))
             (new-indent-delta (+ indent-delta (- new-indent orig-indent))))
        (parinferlib--replace-within-line line-no 0 orig-indent indent-str)
        (puthash :x new-indent parinferlib--result)
        (puthash :indentDelta new-indent-delta parinferlib--result)))))

(defun parinferlib--try-preview-cursor-scope ()
  (when (gethash :canPreviewCursorScope parinferlib--result)
    (let ((cursor-x (gethash :cursorX parinferlib--result))
          (cursor-line (gethash :cursorLine parinferlib--result))
          (result-x (gethash :x parinferlib--result)))
      (when (> cursor-x result-x)
        (parinferlib--correct-paren-trail cursor-x)
        (parinferlib--reset-paren-trail cursor-line cursor-x))
      (puthash :canPreviewCursorScope nil parinferlib--result))))

(defun parinferlib--on-indent ()
  (puthash :trackingIndent nil parinferlib--result)
  (when (gethash :quoteDanger parinferlib--result)
    (throw 'parinferlib-error (parinferlib--create-error 'quote-danger nil nil)))
  (let ((mode (gethash :mode parinferlib--result))
        (x (gethash :x parinferlib--result)))
    (when (equal mode :indent)
      (parinferlib--try-preview-cursor-scope)
      (parinferlib--correct-paren-trail x))
    (when (equal mode :paren)
      (parinferlib--correct-indent))))

(defun parinferlib--on-leading-close-paren ()
  (puthash :skipChar t parinferlib--result)
  (puthash :trackingIndent t parinferlib--result)
  (when (equal :paren (gethash :mode parinferlib--result))
    (let* ((paren-stack (gethash :parenStack parinferlib--result))
           (ch (gethash :ch parinferlib--result)))
      (when (parinferlib--valid-close-paren? paren-stack ch)
        (if (parinferlib--cursor-on-left?)
          (progn (puthash :skipChar nil parinferlib--result)
                 (parinferlib--on-indent))
          (parinferlib--append-paren-trail))))))

(defun parinferlib--check-indent ()
  (let ((ch (gethash :ch parinferlib--result))
        (result-x (gethash :x parinferlib--result))
        (cursor-x (gethash :cursorX parinferlib--result))
        (line-no (gethash :lineNo parinferlib--result)))
    (cond ((parinferlib--close-paren? ch)
           (parinferlib--on-leading-close-paren))

          ((string= ch parinferlib--SEMICOLON)
           (puthash :trackingIndent nil parinferlib--result))

          ((not (or (string= ch parinferlib--NEWLINE)
                    (string= ch parinferlib--BLANK_SPACE)
                    (string= ch parinferlib--TAB)))
           (parinferlib--on-indent)))))

(defun parinferlib--init-preview-cursor-scope ()
  (let* ((preview-cursor-scope (gethash :previewCursorScope parinferlib--result))
         (cursor-line (gethash :cursorLine parinferlib--result))
         (line-no (gethash :lineNo parinferlib--result))
         (lines (gethash :lines parinferlib--result))
         (line (aref lines line-no))
         (semicolon-x (string-match ";" line))
         (cursor-x (gethash :cursorX parinferlib--result)))
    (when (and preview-cursor-scope
               (equal cursor-line line-no))
      (puthash :canPreviewCursorScope
               (and (gethash :trackingIndent parinferlib--result)
                    (string-match parinferlib--STANDALONE_PAREN_TRAIL line)
                    (or (not semicolon-x)
                        (<= cursor-x semicolon-x)))
               parinferlib--result))))

(defun parinferlib--init-indent ()
  (let ((mode (gethash :mode parinferlib--result))
        (in-str? (gethash :isInStr parinferlib--result)))
    (when (equal :indent mode)
      ;; length of list > 0 means the same as the list not being null
      (puthash :trackingIndent (and (gethash :parenStack parinferlib--result)
                                    (not in-str?))
               parinferlib--result)
      (parinferlib--init-preview-cursor-scope))
    (when (equal :paren mode)
       (puthash :trackingIndent (not in-str?) parinferlib--result))))

(defun parinferlib--set-tab-stops ()
  (let ((cursor-line (gethash :cursorLine parinferlib--result))
        (line-no (gethash :lineNo parinferlib--result))
        (mode (gethash :mode parinferlib--result)))
    (when (and (equal cursor-line line-no)
               (equal :indent mode))
      (let ((current-stops (gethash :tabStops parinferlib--result))
            (new-stops '()))
        (dolist (stackel (gethash :parenStack parinferlib--result))
          (let ((new-stop (list :ch (parinferlib--stack-elem-ch stackel)
                                :line-no (parinferlib--stack-elem-line-no stackel)
                                :x (parinferlib--stack-elem-x stackel))))
            (setq new-stops (push new-stop new-stops))))
        (puthash :tabStops (append current-stops new-stops) parinferlib--result)))))

;;------------------------------------------------------------------------------
;; High-level processing functions
;;------------------------------------------------------------------------------

(defun parinferlib--process-char (ch)
  (let* ((orig-ch ch)
         (mode (gethash :mode parinferlib--result)))
    (puthash :ch ch parinferlib--result)
    (puthash :skipChar nil parinferlib--result)

    (when (equal :paren mode)
      (parinferlib--handle-cursor-delta))

    (when (gethash :trackingIndent parinferlib--result)
      (parinferlib--check-indent))

    (if (gethash :skipChar parinferlib--result)
      (puthash :ch "" parinferlib--result)
      (progn (parinferlib--on-char)
             (parinferlib--update-paren-trail-bounds)))

    (parinferlib--commit-char orig-ch)))

(defun parinferlib--process-line (line)
  "Process one line.

LINE: the line content.

Reads from and writes to `parinferlib--result' in the current
buffer."
  (parinferlib--init-line line)
  (parinferlib--init-indent)
  (parinferlib--set-tab-stops)
  (let* ((i 0)
         (chars (concat line parinferlib--NEWLINE))
         (chars-length (length chars)))
    (while (< i chars-length)
      (parinferlib--process-char (string (aref chars i)))
      (setq i (1+ i))))

  (when (equal (gethash :lineNo parinferlib--result)
               (gethash :parenTrailLineNo parinferlib--result))
    (parinferlib--finish-new-paren-trail)))

(defun parinferlib--finalize-result ()
  (when (gethash :quoteDanger parinferlib--result)
    (throw 'parinferlib-error
           (parinferlib--create-error 'quote-danger nil nil)))
  (when (gethash :isInStr parinferlib--result)
    (throw 'parinferlib-error
           (parinferlib--create-error 'unclosed-quote nil nil)))
  (let* ((paren-stack (gethash :parenStack parinferlib--result))
         (mode (gethash :mode parinferlib--result)))
    (when paren-stack
      (when (equal mode :paren)
        (let* ((paren-stack (gethash :parenStack parinferlib--result))
               (opener (car paren-stack))
               (opener-line-no (parinferlib--stack-elem-line-no opener))
               (opener-x (parinferlib--stack-elem-x opener)))
          (throw 'parinferlib-error
                 (parinferlib--create-error 'unclosed-paren opener-line-no opener-x))))
      (when (equal mode :indent)
        (puthash :x 0 parinferlib--result)
        (parinferlib--on-indent))))
  (puthash :success t parinferlib--result))

(defun parinferlib--process-error (err)
  "Set `:success' and `:error' properties of `parinferlib--result' according to ERR."
  (puthash :success nil parinferlib--result)
  (puthash :error err parinferlib--result))

(defun parinferlib--process-text (text mode options)
  "Process TEXT in MODE with OPTIONS.
Writes to the `parinferlib--result' variable."
  (parinferlib--create-initial-result text mode options)
  (let* ((orig-lines (gethash :origLines parinferlib--result))
         (lines-length (length orig-lines))
         (i 0)
         (err (catch 'parinferlib-error
                (while (< i lines-length)
                  (parinferlib--process-line (aref orig-lines i))
                  (setq i (1+ i)))
                (parinferlib--finalize-result)
                nil)))
    (when err
      (parinferlib--process-error err))))

(defun parinferlib--get-changed-lines (result)
  (let* ((orig-lines (gethash :origLines result))
         (lines (gethash :lines result))
         (lines-length (min (length orig-lines) (length lines)))
         (changed-lines nil))
    (dotimes (i lines-length changed-lines)
      (let ((line (aref lines i))
            (orig-line (aref orig-lines i)))
        (unless (string= line orig-line)
          (push (list :line-no i :line line) changed-lines))))))

(defun parinferlib--public-result ()
  "Convert `parinferlib--result' to the public API."
  (let ((result parinferlib--result))
    (if (gethash :success result)
        (let* ((lines (gethash :lines result))
               (result-text (mapconcat 'identity lines parinferlib--NEWLINE))
               (cursor-x (gethash :cursorX result))
               (tab-stops (gethash :tabStops result)))
          (list :success t
                :cursor-x cursor-x
                :text result-text
                :changed-lines (parinferlib--get-changed-lines result)
                :tab-stops tab-stops))
      (let ((orig-text (gethash :origText result))
            (public-error (gethash :error result))
            (orig-cursor-x (gethash :origCursorX result)))
        (list :success nil
              :text orig-text
              :cursor-x orig-cursor-x
              :error public-error)))))

;;------------------------------------------------------------------------------
;; Public API
;;------------------------------------------------------------------------------

(defun parinferlib-indent-mode (text &optional options)
  "Indent Mode public function.

TEXT should be a string to process with Parinfer.
OPTIONS should be a plist; see README.md for all options."
  (with-temp-buffer
    ;; (insert text)
    ;; (goto-char (point-min))
    (parinferlib--process-text text :indent options)
    (parinferlib--public-result)))

(defun parinferlib-paren-mode (text &optional options)
  "Paren Mode public function.

TEXT should be a string to process with Parinfer.
OPTIONS should be a plist; see README.md for all options."
  (with-temp-buffer
    ;; (insert text)
    ;; (goto-char (point-min))
    (parinferlib--process-text text :paren options)
    (parinferlib--public-result)))

(provide 'parinferlib)

;;; parinferlib.el ends here
