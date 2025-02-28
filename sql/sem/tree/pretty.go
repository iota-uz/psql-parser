// Copyright 2018 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

package tree

import (
	"bytes"
	types2 "github.com/iota-uz/psql-parser/sql/types"
	"github.com/iota-uz/psql-parser/util/json"
	pretty2 "github.com/iota-uz/psql-parser/util/pretty"
	"strings"

	"github.com/cockroachdb/errors"
)

// This file contains methods that convert statements to pretty Docs (a tree
// structure that can be pretty printed at a specific line width). Nodes
// implement the docer interface to allow this conversion. In general,
// a node implements doc by copying its Format method and returning a Doc
// structure instead of writing to a buffer. Some guidelines are below.
//
// Nodes should not precede themselves with a space. Instead, the parent
// structure should correctly add spaces when needed.
//
// nestName should be used for most `KEYWORD <expr>` constructs.
//
// Nodes that never need to line break or for which the Format method already
// produces a compact representation should not implement doc, but instead
// rely on the default fallback that uses .Format. Examples include datums
// and constants.

// PrettyCfg holds configuration for pretty printing statements.
type PrettyCfg struct {
	// LineWidth is the desired maximum line width.
	LineWidth int
	// TabWidth is the amount of spaces to use for tabs when UseTabs is
	// false.
	TabWidth int
	// Align, when set to another value than PrettyNoAlign, uses
	// alignment for some constructs as a first choice. If not set or if
	// the line width is insufficient, nesting is used instead.
	Align PrettyAlignMode
	// UseTabs indicates whether to use tab chars to signal indentation.
	UseTabs bool
	// Simplify, when set, removes extraneous parentheses.
	Simplify bool
	// Case, if set, transforms case-insensitive strings (like SQL keywords).
	Case func(string) string
	// JSONFmt, when set, pretty-prints strings that are asserted or cast
	// to JSON.
	JSONFmt bool
}

// DefaultPrettyCfg returns a PrettyCfg with the default
// configuration.
func DefaultPrettyCfg() PrettyCfg {
	return PrettyCfg{
		LineWidth: 60,
		Simplify:  true,
		TabWidth:  4,
		UseTabs:   true,
		Align:     PrettyNoAlign, // TODO(knz): I really want this to be AlignAndDeindent
	}
}

// PrettyAlignMode directs which alignment mode to use.
//
// TODO(knz/mjibson): this variety of options currently exists so as
// to enable comparisons and gauging individual preferences. We should
// aim to remove some or all of these options in the future.
type PrettyAlignMode int

const (
	// PrettyNoAlign disables alignment.
	PrettyNoAlign PrettyAlignMode = 0
	// PrettyAlignOnly aligns sub-clauses only and preserves the
	// hierarchy of logical operators.
	PrettyAlignOnly = 1
	// PrettyAlignAndDeindent does the work of PrettyAlignOnly and also
	// de-indents AND and OR operators.
	PrettyAlignAndDeindent = 2
	// PrettyAlignAndExtraIndent does the work of PrettyAlignOnly and
	// also extra indents the operands of AND and OR operators so
	// that they appear aligned but also indented.
	PrettyAlignAndExtraIndent = 3
)

// keywordWithText returns a pretty.Keyword with left and/or right
// sides concat'd as a pretty.Text.
func (p *PrettyCfg) keywordWithText(left, keyword, right string) pretty2.Doc {
	doc := pretty2.Keyword(keyword)
	if left != "" {
		doc = pretty2.Concat(pretty2.Text(left), doc)
	}
	if right != "" {
		doc = pretty2.Concat(doc, pretty2.Text(right))
	}
	return doc
}

func (p *PrettyCfg) bracket(l string, d pretty2.Doc, r string) pretty2.Doc {
	return p.bracketDoc(pretty2.Text(l), d, pretty2.Text(r))
}

func (p *PrettyCfg) bracketDoc(l, d, r pretty2.Doc) pretty2.Doc {
	return pretty2.BracketDoc(l, d, r)
}

func (p *PrettyCfg) bracketKeyword(
	leftKeyword, leftParen string, inner pretty2.Doc, rightParen, rightKeyword string,
) pretty2.Doc {
	var left, right pretty2.Doc
	if leftKeyword != "" {
		left = p.keywordWithText("", leftKeyword, leftParen)
	} else {
		left = pretty2.Text(leftParen)
	}
	if rightKeyword != "" {
		right = p.keywordWithText(rightParen, rightKeyword, "")
	} else {
		right = pretty2.Text(rightParen)
	}
	return p.bracketDoc(left, inner, right)
}

// Pretty pretty prints stmt with default options.
func Pretty(stmt NodeFormatter) string {
	cfg := DefaultPrettyCfg()
	return cfg.Pretty(stmt)
}

// Pretty pretty prints stmt with specified options.
func (p *PrettyCfg) Pretty(stmt NodeFormatter) string {
	doc := p.Doc(stmt)
	return pretty2.Pretty(doc, p.LineWidth, p.UseTabs, p.TabWidth, p.Case)
}

// Doc converts f (generally a Statement) to a pretty.Doc. If f does not have a
// native conversion, its .Format representation is used as a simple Text Doc.
func (p *PrettyCfg) Doc(f NodeFormatter) pretty2.Doc {
	if f, ok := f.(docer); ok {
		doc := f.doc(p)
		return doc
	}
	return p.docAsString(f)
}

func (p *PrettyCfg) docAsString(f NodeFormatter) pretty2.Doc {
	const prettyFlags = FmtShowPasswords | FmtParsable
	txt := AsStringWithFlags(f, prettyFlags)
	return pretty2.Text(strings.TrimSpace(txt))
}

func (p *PrettyCfg) nestUnder(a, b pretty2.Doc) pretty2.Doc {
	if p.Align != PrettyNoAlign {
		return pretty2.AlignUnder(a, b)
	}
	return pretty2.NestUnder(a, b)
}

func (p *PrettyCfg) rlTable(rows ...pretty2.TableRow) pretty2.Doc {
	alignment := pretty2.TableNoAlign
	if p.Align != PrettyNoAlign {
		alignment = pretty2.TableRightAlignFirstColumn
	}
	return pretty2.Table(alignment, pretty2.Keyword, rows...)
}

func (p *PrettyCfg) llTable(docFn func(string) pretty2.Doc, rows ...pretty2.TableRow) pretty2.Doc {
	alignment := pretty2.TableNoAlign
	if p.Align != PrettyNoAlign {
		alignment = pretty2.TableLeftAlignFirstColumn
	}
	return pretty2.Table(alignment, docFn, rows...)
}

func (p *PrettyCfg) row(lbl string, d pretty2.Doc) pretty2.TableRow {
	return pretty2.TableRow{Label: lbl, Doc: d}
}

var emptyRow = pretty2.TableRow{}

func (p *PrettyCfg) unrow(r pretty2.TableRow) pretty2.Doc {
	if r.Doc == nil {
		return pretty2.Nil
	}
	if r.Label == "" {
		return r.Doc
	}
	return p.nestUnder(pretty2.Text(r.Label), r.Doc)
}

func (p *PrettyCfg) commaSeparated(d ...pretty2.Doc) pretty2.Doc {
	return pretty2.Join(",", d...)
}

func (p *PrettyCfg) joinNestedOuter(lbl string, d ...pretty2.Doc) pretty2.Doc {
	if len(d) == 0 {
		return pretty2.Nil
	}
	switch p.Align {
	case PrettyAlignAndDeindent:
		return pretty2.JoinNestedOuter(lbl, pretty2.Keyword, d...)
	case PrettyAlignAndExtraIndent:
		items := make([]pretty2.TableRow, len(d))
		for i, dd := range d {
			if i > 0 {
				items[i].Label = lbl
			}
			items[i].Doc = dd
		}
		return pretty2.Table(pretty2.TableRightAlignFirstColumn, pretty2.Keyword, items...)
	default:
		return pretty2.JoinNestedRight(pretty2.Keyword(lbl), d...)
	}
}

// docer is implemented by nodes that can convert themselves into
// pretty.Docs. If nodes cannot, node.Format is used instead as a Text Doc.
type docer interface {
	doc(*PrettyCfg) pretty2.Doc
}

// tableDocer is implemented by nodes that can convert themselves
// into []pretty.TableRow, i.e. a table.
type tableDocer interface {
	docTable(*PrettyCfg) []pretty2.TableRow
}

func (node SelectExprs) doc(p *PrettyCfg) pretty2.Doc {
	d := make([]pretty2.Doc, len(node))
	for i, e := range node {
		d[i] = e.doc(p)
	}
	return p.commaSeparated(d...)
}

func (node SelectExpr) doc(p *PrettyCfg) pretty2.Doc {
	e := node.Expr
	if p.Simplify {
		e = StripParens(e)
	}
	d := p.Doc(e)
	if node.As != "" {
		d = p.nestUnder(
			d,
			pretty2.Concat(p.keywordWithText("", "AS", " "), p.Doc(&node.As)),
		)
	}
	return d
}

func (node TableExprs) doc(p *PrettyCfg) pretty2.Doc {
	if len(node) == 0 {
		return pretty2.Nil
	}
	d := make([]pretty2.Doc, len(node))
	for i, e := range node {
		if p.Simplify {
			e = StripTableParens(e)
		}
		d[i] = p.Doc(e)
	}
	return p.commaSeparated(d...)
}

func (node *Where) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *Where) docRow(p *PrettyCfg) pretty2.TableRow {
	if node == nil {
		return emptyRow
	}
	e := node.Expr
	if p.Simplify {
		e = StripParens(e)
	}
	return p.row(node.Type, p.Doc(e))
}

func (node *GroupBy) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *GroupBy) docRow(p *PrettyCfg) pretty2.TableRow {
	if len(*node) == 0 {
		return emptyRow
	}
	d := make([]pretty2.Doc, len(*node))
	for i, e := range *node {
		// Beware! The GROUP BY items should never be simplified by
		// stripping parentheses, because parentheses there are
		// semantically important.
		d[i] = p.Doc(e)
	}
	return p.row("GROUP BY", p.commaSeparated(d...))
}

// flattenOp populates a slice with all the leaves operands of an expression
// tree where all the nodes satisfy the given predicate.
func (p *PrettyCfg) flattenOp(
	e Expr,
	pred func(e Expr, recurse func(e Expr)) bool,
	formatOperand func(e Expr) pretty2.Doc,
	in []pretty2.Doc,
) []pretty2.Doc {
	if ok := pred(e, func(sub Expr) {
		in = p.flattenOp(sub, pred, formatOperand, in)
	}); ok {
		return in
	}
	return append(in, formatOperand(e))
}

func (p *PrettyCfg) peelAndOrOperand(e Expr) Expr {
	if !p.Simplify {
		return e
	}
	stripped := StripParens(e)
	switch stripped.(type) {
	case *BinaryExpr, *ComparisonExpr, *RangeCond, *FuncExpr, *IndirectionExpr,
		*UnaryExpr, *AnnotateTypeExpr, *CastExpr, *ColumnItem, *UnresolvedName:
		// All these expressions have higher precedence than binary
		// expressions.
		return stripped
	}
	// Everything else - we don't know. Be conservative and keep the
	// original form.
	return e
}

func (node *AndExpr) doc(p *PrettyCfg) pretty2.Doc {
	pred := func(e Expr, recurse func(e Expr)) bool {
		if a, ok := e.(*AndExpr); ok {
			recurse(a.Left)
			recurse(a.Right)
			return true
		}
		return false
	}
	formatOperand := func(e Expr) pretty2.Doc {
		return p.Doc(p.peelAndOrOperand(e))
	}
	operands := p.flattenOp(node.Left, pred, formatOperand, nil)
	operands = p.flattenOp(node.Right, pred, formatOperand, operands)
	return p.joinNestedOuter("AND", operands...)
}

func (node *OrExpr) doc(p *PrettyCfg) pretty2.Doc {
	pred := func(e Expr, recurse func(e Expr)) bool {
		if a, ok := e.(*OrExpr); ok {
			recurse(a.Left)
			recurse(a.Right)
			return true
		}
		return false
	}
	formatOperand := func(e Expr) pretty2.Doc {
		return p.Doc(p.peelAndOrOperand(e))
	}
	operands := p.flattenOp(node.Left, pred, formatOperand, nil)
	operands = p.flattenOp(node.Right, pred, formatOperand, operands)
	return p.joinNestedOuter("OR", operands...)
}

func (node *Exprs) doc(p *PrettyCfg) pretty2.Doc {
	if node == nil || len(*node) == 0 {
		return pretty2.Nil
	}
	d := make([]pretty2.Doc, len(*node))
	for i, e := range *node {
		if p.Simplify {
			e = StripParens(e)
		}
		d[i] = p.Doc(e)
	}
	return p.commaSeparated(d...)
}

// peelBinaryOperand conditionally (p.Simplify) removes the
// parentheses around an expression. The parentheses are always
// removed in the following conditions:
//   - if the operand is a unary operator (these are always
//     of higher precedence): "(-a) * b" -> "-a * b"
//   - if the operand is a binary operator and its precedence
//     is guaranteed to be higher: "(a * b) + c" -> "a * b + c"
//
// Additionally, iff sameLevel is set, then parentheses are removed
// around any binary operator that has the same precedence level as
// the parent.
// sameLevel can be set:
//
//   - for the left operand of all binary expressions, because
//     (in pg SQL) all binary expressions are left-associative.
//     This rewrites e.g. "(a + b) - c" -> "a + b - c"
//     and "(a - b) + c" -> "a - b + c"
//   - for the right operand when the parent operator is known
//     to be fully associative, e.g.
//     "a + (b - c)" -> "a + b - c" because "+" is fully assoc,
//     but "a - (b + c)" cannot be simplified because "-" is not fully associative.
func (p *PrettyCfg) peelBinaryOperand(e Expr, sameLevel bool, parenPrio int) Expr {
	if !p.Simplify {
		return e
	}
	stripped := StripParens(e)
	switch te := stripped.(type) {
	case *BinaryExpr:
		childPrio := binaryOpPrio[te.Operator]
		if childPrio < parenPrio || (sameLevel && childPrio == parenPrio) {
			return stripped
		}
	case *FuncExpr, *UnaryExpr, *AnnotateTypeExpr, *IndirectionExpr,
		*CastExpr, *ColumnItem, *UnresolvedName:
		// All these expressions have higher precedence than binary expressions.
		return stripped
	}
	// Everything else - we don't know. Be conservative and keep the
	// original form.
	return e
}

func (node *BinaryExpr) doc(p *PrettyCfg) pretty2.Doc {
	// All the binary operators are at least left-associative.
	// So we can always simplify "(a OP b) OP c" to "a OP b OP c".
	parenPrio := binaryOpPrio[node.Operator]
	leftOperand := p.peelBinaryOperand(node.Left, true /*sameLevel*/, parenPrio)
	// If the binary operator is also fully associative,
	// we can also simplify "a OP (b OP c)" to "a OP b OP c".
	opFullyAssoc := binaryOpFullyAssoc[node.Operator]
	rightOperand := p.peelBinaryOperand(node.Right, opFullyAssoc, parenPrio)

	opDoc := pretty2.Text(node.Operator.String())
	var res pretty2.Doc
	if !node.Operator.isPadded() {
		res = pretty2.JoinDoc(opDoc, p.Doc(leftOperand), p.Doc(rightOperand))
	} else {
		pred := func(e Expr, recurse func(e Expr)) bool {
			if b, ok := e.(*BinaryExpr); ok && b.Operator == node.Operator {
				leftSubOperand := p.peelBinaryOperand(b.Left, true /*sameLevel*/, parenPrio)
				rightSubOperand := p.peelBinaryOperand(b.Right, opFullyAssoc, parenPrio)
				recurse(leftSubOperand)
				recurse(rightSubOperand)
				return true
			}
			return false
		}
		formatOperand := func(e Expr) pretty2.Doc {
			return p.Doc(e)
		}
		operands := p.flattenOp(leftOperand, pred, formatOperand, nil)
		operands = p.flattenOp(rightOperand, pred, formatOperand, operands)
		res = pretty2.JoinNestedRight(
			opDoc, operands...)
	}
	return pretty2.Group(res)
}

func (node *ParenExpr) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracket("(", p.Doc(node.Expr), ")")
}

func (node *ParenSelect) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracket("(", p.Doc(node.Select), ")")
}

func (node *ParenTableExpr) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracket("(", p.Doc(node.Expr), ")")
}

func (node *Limit) doc(p *PrettyCfg) pretty2.Doc {
	res := pretty2.Nil
	for i, r := range node.docTable(p) {
		if r.Doc != nil {
			if i > 0 {
				res = pretty2.Concat(res, pretty2.Line)
			}
			res = pretty2.Concat(res, p.nestUnder(pretty2.Text(r.Label), r.Doc))
		}
	}
	return res
}

func (node *Limit) docTable(p *PrettyCfg) []pretty2.TableRow {
	if node == nil {
		return nil
	}
	res := make([]pretty2.TableRow, 0, 2)
	if node.Count != nil {
		e := node.Count
		if p.Simplify {
			e = StripParens(e)
		}
		res = append(res, p.row("LIMIT", p.Doc(e)))
	} else if node.LimitAll {
		res = append(res, p.row("LIMIT", pretty2.Keyword("ALL")))
	}
	if node.Offset != nil {
		e := node.Offset
		if p.Simplify {
			e = StripParens(e)
		}
		res = append(res, p.row("OFFSET", p.Doc(e)))
	}
	return res
}

func (node *OrderBy) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *OrderBy) docRow(p *PrettyCfg) pretty2.TableRow {
	if node == nil || len(*node) == 0 {
		return emptyRow
	}
	d := make([]pretty2.Doc, len(*node))
	for i, e := range *node {
		// Beware! The ORDER BY items should never be simplified,
		// because parentheses there are semantically important.
		d[i] = p.Doc(e)
	}
	return p.row("ORDER BY", p.commaSeparated(d...))
}

func (node *Select) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *Select) docTable(p *PrettyCfg) []pretty2.TableRow {
	items := make([]pretty2.TableRow, 0, 9)
	items = append(items, node.With.docRow(p))
	if s, ok := node.Select.(tableDocer); ok {
		items = append(items, s.docTable(p)...)
	} else {
		items = append(items, p.row("", p.Doc(node.Select)))
	}
	items = append(items, node.OrderBy.docRow(p))
	items = append(items, node.Limit.docTable(p)...)
	items = append(items, node.Locking.docTable(p)...)
	return items
}

func (node *SelectClause) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *SelectClause) docTable(p *PrettyCfg) []pretty2.TableRow {
	if node.TableSelect {
		return []pretty2.TableRow{p.row("TABLE", p.Doc(node.From.Tables[0]))}
	}
	exprs := node.Exprs.doc(p)
	if node.Distinct {
		if node.DistinctOn != nil {
			exprs = pretty2.ConcatLine(p.Doc(&node.DistinctOn), exprs)
		} else {
			exprs = pretty2.ConcatLine(pretty2.Keyword("DISTINCT"), exprs)
		}
	}
	return []pretty2.TableRow{
		p.row("SELECT", exprs),
		node.From.docRow(p),
		node.Where.docRow(p),
		node.GroupBy.docRow(p),
		node.Having.docRow(p),
		node.Window.docRow(p),
	}
}

func (node *From) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *From) docRow(p *PrettyCfg) pretty2.TableRow {
	if node == nil || len(node.Tables) == 0 {
		return emptyRow
	}
	d := node.Tables.doc(p)
	if node.AsOf.Expr != nil {
		d = p.nestUnder(
			d,
			p.Doc(&node.AsOf),
		)
	}
	return p.row("FROM", d)
}

func (node *Window) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *Window) docRow(p *PrettyCfg) pretty2.TableRow {
	if node == nil || len(*node) == 0 {
		return emptyRow
	}
	d := make([]pretty2.Doc, len(*node))
	for i, e := range *node {
		d[i] = pretty2.Fold(pretty2.Concat,
			pretty2.Text(e.Name.String()),
			p.keywordWithText(" ", "AS", " "),
			p.Doc(e),
		)
	}
	return p.row("WINDOW", p.commaSeparated(d...))
}

func (node *With) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *With) docRow(p *PrettyCfg) pretty2.TableRow {
	if node == nil {
		return emptyRow
	}
	d := make([]pretty2.Doc, len(node.CTEList))
	for i, cte := range node.CTEList {
		d[i] = p.nestUnder(
			p.Doc(&cte.Name),
			p.bracketKeyword("AS", " (", p.Doc(cte.Stmt), ")", ""),
		)
	}
	kw := "WITH"
	if node.Recursive {
		kw = "WITH RECURSIVE"
	}
	return p.row(kw, p.commaSeparated(d...))
}

func (node *Subquery) doc(p *PrettyCfg) pretty2.Doc {
	d := pretty2.Text("<unknown>")
	if node.Select != nil {
		d = p.Doc(node.Select)
	}
	if node.Exists {
		d = pretty2.Concat(
			pretty2.Keyword("EXISTS"),
			d,
		)
	}
	return d
}

func (node *AliasedTableExpr) doc(p *PrettyCfg) pretty2.Doc {
	d := p.Doc(node.Expr)
	if node.Lateral {
		d = pretty2.Concat(
			p.keywordWithText("", "LATERAL", " "),
			d,
		)
	}
	if node.IndexFlags != nil {
		d = pretty2.Concat(
			d,
			p.Doc(node.IndexFlags),
		)
	}
	if node.Ordinality {
		d = pretty2.Concat(
			d,
			p.keywordWithText(" ", "WITH ORDINALITY", ""),
		)
	}
	if node.As.Alias != "" {
		d = p.nestUnder(
			d,
			pretty2.Concat(
				p.keywordWithText("", "AS", " "),
				p.Doc(&node.As),
			),
		)
	}
	return d
}

func (node *FuncExpr) doc(p *PrettyCfg) pretty2.Doc {
	d := p.Doc(&node.Func)

	if len(node.Exprs) > 0 {
		args := node.Exprs.doc(p)
		if node.Type != 0 {
			args = pretty2.ConcatLine(
				pretty2.Text(funcTypeName[node.Type]),
				args,
			)
		}

		if len(node.OrderBy) > 0 {
			args = pretty2.ConcatSpace(args, node.OrderBy.doc(p))
		}
		d = pretty2.Concat(d, p.bracket("(", args, ")"))
	} else {
		d = pretty2.Concat(d, pretty2.Text("()"))
	}
	if node.Filter != nil {
		d = pretty2.Fold(pretty2.ConcatSpace,
			d,
			pretty2.Keyword("FILTER"),
			p.bracket("(",
				p.nestUnder(pretty2.Keyword("WHERE"), p.Doc(node.Filter)),
				")"))
	}
	if window := node.WindowDef; window != nil {
		var over pretty2.Doc
		if window.Name != "" {
			over = p.Doc(&window.Name)
		} else {
			over = p.Doc(window)
		}
		d = pretty2.Fold(pretty2.ConcatSpace,
			d,
			pretty2.Keyword("OVER"),
			over,
		)
	}
	return d
}

func (node *WindowDef) doc(p *PrettyCfg) pretty2.Doc {
	rows := make([]pretty2.TableRow, 0, 4)
	if node.RefName != "" {
		rows = append(rows, p.row("", p.Doc(&node.RefName)))
	}
	if len(node.Partitions) > 0 {
		rows = append(rows, p.row("PARTITION BY", p.Doc(&node.Partitions)))
	}
	if len(node.OrderBy) > 0 {
		rows = append(rows, node.OrderBy.docRow(p))
	}
	if node.Frame != nil {
		rows = append(rows, node.Frame.docRow(p))
	}
	if len(rows) == 0 {
		return pretty2.Text("()")
	}
	return p.bracket("(", p.rlTable(rows...), ")")
}

func (wf *WindowFrame) docRow(p *PrettyCfg) pretty2.TableRow {
	kw := "RANGE"
	if wf.Mode == ROWS {
		kw = "ROWS"
	} else if wf.Mode == GROUPS {
		kw = "GROUPS"
	}
	d := p.Doc(wf.Bounds.StartBound)
	if wf.Bounds.EndBound != nil {
		d = p.rlTable(
			p.row("BETWEEN", d),
			p.row("AND", p.Doc(wf.Bounds.EndBound)),
		)
	}
	if wf.Exclusion != NoExclusion {
		d = pretty2.Stack(d, p.Doc(wf.Exclusion))
	}
	return p.row(kw, d)
}

func (node *WindowFrameBound) doc(p *PrettyCfg) pretty2.Doc {
	switch node.BoundType {
	case UnboundedPreceding:
		return pretty2.Keyword("UNBOUNDED PRECEDING")
	case OffsetPreceding:
		return pretty2.ConcatSpace(p.Doc(node.OffsetExpr), pretty2.Keyword("PRECEDING"))
	case CurrentRow:
		return pretty2.Keyword("CURRENT ROW")
	case OffsetFollowing:
		return pretty2.ConcatSpace(p.Doc(node.OffsetExpr), pretty2.Keyword("FOLLOWING"))
	case UnboundedFollowing:
		return pretty2.Keyword("UNBOUNDED FOLLOWING")
	default:
		panic(errors.AssertionFailedf("unexpected type %d", errors.Safe(node.BoundType)))
	}
}

func (node *LockingClause) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *LockingClause) docTable(p *PrettyCfg) []pretty2.TableRow {
	items := make([]pretty2.TableRow, len(*node))
	for i, n := range *node {
		items[i] = p.row("", p.Doc(n))
	}
	return items
}

func (node *LockingItem) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *LockingItem) docTable(p *PrettyCfg) []pretty2.TableRow {
	if node.Strength == ForNone {
		return nil
	}
	items := make([]pretty2.TableRow, 0, 3)
	items = append(items, node.Strength.docTable(p)...)
	if len(node.Targets) > 0 {
		items = append(items, p.row("OF", p.Doc(&node.Targets)))
	}
	items = append(items, node.WaitPolicy.docTable(p)...)
	return items
}

func (node LockingStrength) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node LockingStrength) docTable(p *PrettyCfg) []pretty2.TableRow {
	str := node.String()
	if str == "" {
		return nil
	}
	return []pretty2.TableRow{p.row("", pretty2.Keyword(str))}
}

func (node LockingWaitPolicy) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node LockingWaitPolicy) docTable(p *PrettyCfg) []pretty2.TableRow {
	str := node.String()
	if str == "" {
		return nil
	}
	return []pretty2.TableRow{p.row("", pretty2.Keyword(str))}
}

func (p *PrettyCfg) peelCompOperand(e Expr) Expr {
	if !p.Simplify {
		return e
	}
	stripped := StripParens(e)
	switch stripped.(type) {
	case *FuncExpr, *IndirectionExpr, *UnaryExpr,
		*AnnotateTypeExpr, *CastExpr, *ColumnItem, *UnresolvedName:
		return stripped
	}
	return e
}

func (node *ComparisonExpr) doc(p *PrettyCfg) pretty2.Doc {
	opStr := node.Operator.String()
	if node.Operator == IsDistinctFrom && (node.Right == DNull || node.Right == DBoolTrue || node.Right == DBoolFalse) {
		opStr = "IS NOT"
	} else if node.Operator == IsNotDistinctFrom && (node.Right == DNull || node.Right == DBoolTrue || node.Right == DBoolFalse) {
		opStr = "IS"
	}
	opDoc := pretty2.Keyword(opStr)
	if node.Operator.hasSubOperator() {
		opDoc = pretty2.ConcatSpace(pretty2.Text(node.SubOperator.String()), opDoc)
	}
	return pretty2.Group(
		pretty2.JoinNestedRight(
			opDoc,
			p.Doc(p.peelCompOperand(node.Left)),
			p.Doc(p.peelCompOperand(node.Right))))
}

func (node *AliasClause) doc(p *PrettyCfg) pretty2.Doc {
	d := pretty2.Text(node.Alias.String())
	if len(node.Cols) != 0 {
		d = p.nestUnder(d, p.bracket("(", p.Doc(&node.Cols), ")"))
	}
	return d
}

func (node *JoinTableExpr) doc(p *PrettyCfg) pretty2.Doc {
	//  buf will contain the fully populated sequence of join keywords.
	var buf bytes.Buffer
	cond := pretty2.Nil
	if _, isNatural := node.Cond.(NaturalJoinCond); isNatural {
		// Natural joins have a different syntax:
		//   "<a> NATURAL <join_type> [<join_hint>] JOIN <b>"
		buf.WriteString("NATURAL ")
	} else {
		// Regular joins:
		//   "<a> <join type> [<join hint>] JOIN <b>"
		if node.Cond != nil {
			cond = p.Doc(node.Cond)
		}
	}

	if node.JoinType != "" {
		buf.WriteString(node.JoinType)
		buf.WriteByte(' ')
		if node.Hint != "" {
			buf.WriteString(node.Hint)
			buf.WriteByte(' ')
		}
	}
	buf.WriteString("JOIN")

	return p.joinNestedOuter(
		buf.String(),
		p.Doc(node.Left),
		pretty2.ConcatSpace(p.Doc(node.Right), cond))
}

func (node *OnJoinCond) doc(p *PrettyCfg) pretty2.Doc {
	e := node.Expr
	if p.Simplify {
		e = StripParens(e)
	}
	return p.nestUnder(pretty2.Keyword("ON"), p.Doc(e))
}

func (node *Insert) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 0, 8)
	items = append(items, node.With.docRow(p))
	kw := "INSERT"
	if node.OnConflict.IsUpsertAlias() {
		kw = "UPSERT"
	}
	items = append(items, p.row(kw, pretty2.Nil))

	into := p.Doc(node.Table)
	if node.Columns != nil {
		into = p.nestUnder(into, p.bracket("(", p.Doc(&node.Columns), ")"))
	}
	items = append(items, p.row("INTO", into))

	if node.DefaultValues() {
		items = append(items, p.row("", pretty2.Keyword("DEFAULT VALUES")))
	} else {
		items = append(items, node.Rows.docTable(p)...)
	}

	if node.OnConflict != nil && !node.OnConflict.IsUpsertAlias() {
		cond := pretty2.Nil
		if len(node.OnConflict.Columns) > 0 {
			cond = p.bracket("(", p.Doc(&node.OnConflict.Columns), ")")
		}
		items = append(items, p.row("ON CONFLICT", cond))

		if node.OnConflict.DoNothing {
			items = append(items, p.row("DO", pretty2.Keyword("NOTHING")))
		} else {
			items = append(items, p.row("DO",
				p.nestUnder(pretty2.Keyword("UPDATE SET"), p.Doc(&node.OnConflict.Exprs))))
			if node.OnConflict.Where != nil {
				items = append(items, node.OnConflict.Where.docRow(p))
			}
		}
	}

	items = append(items, p.docReturning(node.Returning))
	return p.rlTable(items...)
}

func (node *NameList) doc(p *PrettyCfg) pretty2.Doc {
	d := make([]pretty2.Doc, len(*node))
	for i, n := range *node {
		d[i] = p.Doc(&n)
	}
	return p.commaSeparated(d...)
}

func (node *CastExpr) doc(p *PrettyCfg) pretty2.Doc {
	typ := pretty2.Text(node.Type.SQLString())

	switch node.SyntaxMode {
	case CastPrepend:
		// This is a special case for things like INTERVAL '1s'. These only work
		// with string constats; if the underlying expression was changed, we fall
		// back to the short syntax.
		if _, ok := node.Expr.(*StrVal); ok {
			return pretty2.Fold(pretty2.Concat,
				typ,
				pretty2.Text(" "),
				p.Doc(node.Expr),
			)
		}
		fallthrough
	case CastShort:
		switch node.Type.Family() {
		case types2.JsonFamily:
			if sv, ok := node.Expr.(*StrVal); ok && p.JSONFmt {
				return p.jsonCast(sv, "::", node.Type)
			}
		}
		return pretty2.Fold(pretty2.Concat,
			p.exprDocWithParen(node.Expr),
			pretty2.Text("::"),
			typ,
		)
	default:
		if node.Type.Family() == types2.CollatedStringFamily {
			// COLLATE clause needs to go after CAST expression, so create
			// equivalent string type without the locale to get name of string
			// type without the COLLATE.
			strTyp := types2.MakeScalar(
				types2.StringFamily,
				node.Type.Oid(),
				node.Type.Precision(),
				node.Type.Width(),
				"", /* locale */
			)
			typ = pretty2.Text(strTyp.SQLString())
		}

		ret := pretty2.Fold(pretty2.Concat,
			pretty2.Keyword("CAST"),
			p.bracket(
				"(",
				p.nestUnder(
					p.Doc(node.Expr),
					pretty2.Concat(
						p.keywordWithText("", "AS", " "),
						typ,
					),
				),
				")",
			),
		)

		if node.Type.Family() == types2.CollatedStringFamily {
			ret = pretty2.Fold(pretty2.ConcatSpace,
				ret,
				pretty2.Keyword("COLLATE"),
				pretty2.Text(node.Type.Locale()))
		}
		return ret
	}
}

func (node *ValuesClause) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *ValuesClause) docTable(p *PrettyCfg) []pretty2.TableRow {
	d := make([]pretty2.Doc, len(node.Rows))
	for i := range node.Rows {
		d[i] = p.bracket("(", p.Doc(&node.Rows[i]), ")")
	}
	return []pretty2.TableRow{p.row("VALUES", p.commaSeparated(d...))}
}

func (node *StatementSource) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracket("[", p.Doc(node.Statement), "]")
}

func (node *RowsFromExpr) doc(p *PrettyCfg) pretty2.Doc {
	if p.Simplify && len(node.Items) == 1 {
		return p.Doc(node.Items[0])
	}
	return p.bracketKeyword("ROWS FROM", " (", p.Doc(&node.Items), ")", "")
}

func (node *Array) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracketKeyword("ARRAY", "[", p.Doc(&node.Exprs), "]", "")
}

func (node *Tuple) doc(p *PrettyCfg) pretty2.Doc {
	exprDoc := p.Doc(&node.Exprs)
	if len(node.Exprs) == 1 {
		exprDoc = pretty2.Concat(exprDoc, pretty2.Text(","))
	}
	d := p.bracket("(", exprDoc, ")")
	if len(node.Labels) > 0 {
		labels := make([]pretty2.Doc, len(node.Labels))
		for i, n := range node.Labels {
			labels[i] = p.Doc((*Name)(&n))
		}
		d = p.bracket("(", pretty2.Stack(
			d,
			p.nestUnder(pretty2.Keyword("AS"), p.commaSeparated(labels...)),
		), ")")
	}
	return d
}

func (node *UpdateExprs) doc(p *PrettyCfg) pretty2.Doc {
	d := make([]pretty2.Doc, len(*node))
	for i, n := range *node {
		d[i] = p.Doc(n)
	}
	return p.commaSeparated(d...)
}

func (p *PrettyCfg) exprDocWithParen(e Expr) pretty2.Doc {
	if _, ok := e.(operatorExpr); ok {
		return p.bracket("(", p.Doc(e), ")")
	}
	return p.Doc(e)
}

func (node *Update) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 8)
	items = append(items,
		node.With.docRow(p),
		p.row("UPDATE", p.Doc(node.Table)),
		p.row("SET", p.Doc(&node.Exprs)))
	if len(node.From) > 0 {
		items = append(items,
			p.row("FROM", p.Doc(&node.From)))
	}
	items = append(items,
		node.Where.docRow(p),
		node.OrderBy.docRow(p))
	items = append(items, node.Limit.docTable(p)...)
	items = append(items, p.docReturning(node.Returning))
	return p.rlTable(items...)
}

func (node *Delete) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 6)
	items = append(items,
		node.With.docRow(p),
		p.row("DELETE FROM", p.Doc(node.Table)),
		node.Where.docRow(p),
		node.OrderBy.docRow(p))
	items = append(items, node.Limit.docTable(p)...)
	items = append(items, p.docReturning(node.Returning))
	return p.rlTable(items...)
}

func (p *PrettyCfg) docReturning(node ReturningClause) pretty2.TableRow {
	switch r := node.(type) {
	case *NoReturningClause:
		return p.row("", nil)
	case *ReturningNothing:
		return p.row("RETURNING", pretty2.Keyword("NOTHING"))
	case *ReturningExprs:
		return p.row("RETURNING", p.Doc((*SelectExprs)(r)))
	default:
		panic(errors.AssertionFailedf("unhandled case: %T", node))
	}
}

func (node *Order) doc(p *PrettyCfg) pretty2.Doc {
	var d pretty2.Doc
	if node.OrderType == OrderByColumn {
		d = p.Doc(node.Expr)
	} else {
		if node.Index == "" {
			d = pretty2.ConcatSpace(
				pretty2.Keyword("PRIMARY KEY"),
				p.Doc(&node.Table),
			)
		} else {
			d = pretty2.ConcatSpace(
				pretty2.Keyword("INDEX"),
				pretty2.Fold(pretty2.Concat,
					p.Doc(&node.Table),
					pretty2.Text("@"),
					p.Doc(&node.Index),
				),
			)
		}
	}
	if node.Direction != DefaultDirection {
		d = p.nestUnder(d, pretty2.Text(node.Direction.String()))
	}
	if node.NullsOrder != DefaultNullsOrder {
		d = p.nestUnder(d, pretty2.Text(node.NullsOrder.String()))
	}
	return d
}

func (node *UpdateExpr) doc(p *PrettyCfg) pretty2.Doc {
	d := p.Doc(&node.Names)
	if node.Tuple {
		d = p.bracket("(", d, ")")
	}
	e := node.Expr
	if p.Simplify {
		e = StripParens(e)
	}
	return p.nestUnder(d, pretty2.ConcatSpace(pretty2.Text("="), p.Doc(e)))
}

func (node *CreateTable) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// CREATE [TEMP] TABLE [IF NOT EXISTS] name ( .... ) [AS]
	//     [SELECT ...] - for CREATE TABLE AS
	//     [INTERLEAVE ...]
	//     [PARTITION BY ...]
	//
	title := pretty2.Keyword("CREATE")
	if node.Temporary {
		title = pretty2.ConcatSpace(title, pretty2.Keyword("TEMPORARY"))
	}
	title = pretty2.ConcatSpace(title, pretty2.Keyword("TABLE"))
	if node.IfNotExists {
		title = pretty2.ConcatSpace(title, pretty2.Keyword("IF NOT EXISTS"))
	}
	title = pretty2.ConcatSpace(title, p.Doc(&node.Table))

	if node.As() {
		if len(node.Defs) > 0 {
			title = pretty2.ConcatSpace(title,
				p.bracket("(", p.Doc(&node.Defs), ")"))
		}
		title = pretty2.ConcatSpace(title, pretty2.Keyword("AS"))
	} else {
		title = pretty2.ConcatSpace(title,
			p.bracket("(", p.Doc(&node.Defs), ")"),
		)
	}

	clauses := make([]pretty2.Doc, 0, 2)
	if node.As() {
		clauses = append(clauses, p.Doc(node.AsSource))
	}
	if node.Interleave != nil {
		clauses = append(clauses, p.Doc(node.Interleave))
	}
	if node.PartitionBy != nil {
		clauses = append(clauses, p.Doc(node.PartitionBy))
	}
	if len(clauses) == 0 {
		return title
	}
	return p.nestUnder(title, pretty2.Group(pretty2.Stack(clauses...)))
}

func (node *CreateView) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// CREATE [TEMP] VIEW name ( ... ) AS
	//     SELECT ...
	//
	title := pretty2.Keyword("CREATE")
	if node.Temporary {
		title = pretty2.ConcatSpace(title, pretty2.Keyword("TEMPORARY"))
	}
	title = pretty2.ConcatSpace(title, pretty2.Keyword("VIEW"))
	if node.IfNotExists {
		title = pretty2.ConcatSpace(title, pretty2.Keyword("IF NOT EXISTS"))
	}
	d := pretty2.ConcatSpace(
		title,
		p.Doc(&node.Name),
	)
	if len(node.ColumnNames) > 0 {
		d = pretty2.ConcatSpace(
			d,
			p.bracket("(", p.Doc(&node.ColumnNames), ")"),
		)
	}
	return p.nestUnder(
		pretty2.ConcatSpace(d, pretty2.Keyword("AS")),
		p.Doc(node.AsSource),
	)
}

func (node *TableDefs) doc(p *PrettyCfg) pretty2.Doc {
	// This groups column definitions using a table to get alignment of
	// column names, and separately comma-joins groups of column definitions
	// with constraint definitions.

	defs := *node
	colDefRows := make([]pretty2.TableRow, 0, len(defs))
	items := make([]pretty2.Doc, 0, len(defs))

	for i := 0; i < len(defs); i++ {
		if _, ok := defs[i].(*ColumnTableDef); ok {
			// Group all the subsequent column definitions into a table.
			j := i
			colDefRows = colDefRows[:0]
			for ; j < len(defs); j++ {
				cdef, ok := defs[j].(*ColumnTableDef)
				if !ok {
					break
				}
				colDefRows = append(colDefRows, cdef.docRow(p))
			}
			// Let the outer loop pick up where we left.
			i = j - 1

			// At this point the column definitions form a table, but the comma
			// is missing from each row. We need to add it here. However we
			// need to be careful. Since we're going to add a comma between the
			// set of all column definitions and the other table definitions
			// below (via commaSeparated), we need to ensure the last row does
			// not get a comma.
			for j = 0; j < len(colDefRows)-1; j++ {
				colDefRows[j].Doc = pretty2.Concat(colDefRows[j].Doc, pretty2.Text(","))
			}
			items = append(items, p.llTable(pretty2.Text, colDefRows...))
		} else {
			// Not a column definition, just process normally.
			items = append(items, p.Doc(defs[i]))
		}
	}

	return p.commaSeparated(items...)
}

func (node *CaseExpr) doc(p *PrettyCfg) pretty2.Doc {
	d := make([]pretty2.Doc, 0, len(node.Whens)+3)
	c := pretty2.Keyword("CASE")
	if node.Expr != nil {
		c = pretty2.Group(pretty2.ConcatSpace(c, p.Doc(node.Expr)))
	}
	d = append(d, c)
	for _, when := range node.Whens {
		d = append(d, p.Doc(when))
	}
	if node.Else != nil {
		d = append(d, pretty2.Group(pretty2.ConcatSpace(
			pretty2.Keyword("ELSE"),
			p.Doc(node.Else),
		)))
	}
	d = append(d, pretty2.Keyword("END"))
	return pretty2.Stack(d...)
}

func (node *When) doc(p *PrettyCfg) pretty2.Doc {
	return pretty2.Group(pretty2.ConcatLine(
		pretty2.Group(pretty2.ConcatSpace(
			pretty2.Keyword("WHEN"),
			p.Doc(node.Cond),
		)),
		pretty2.Group(pretty2.ConcatSpace(
			pretty2.Keyword("THEN"),
			p.Doc(node.Val),
		)),
	))
}

func (node *UnionClause) doc(p *PrettyCfg) pretty2.Doc {
	op := node.Type.String()
	if node.All {
		op += " ALL"
	}
	return pretty2.Stack(p.Doc(node.Left), p.nestUnder(pretty2.Keyword(op), p.Doc(node.Right)))
}

func (node *IfErrExpr) doc(p *PrettyCfg) pretty2.Doc {
	var s string
	if node.Else != nil {
		s = "IFERROR"
	} else {
		s = "ISERROR"
	}
	d := []pretty2.Doc{p.Doc(node.Cond)}
	if node.Else != nil {
		d = append(d, p.Doc(node.Else))
	}
	if node.ErrCode != nil {
		d = append(d, p.Doc(node.ErrCode))
	}
	return p.bracketKeyword(s, "(", p.commaSeparated(d...), ")", "")
}

func (node *IfExpr) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracketKeyword("IF", "(",
		p.commaSeparated(
			p.Doc(node.Cond),
			p.Doc(node.True),
			p.Doc(node.Else),
		), ")", "")
}

func (node *NullIfExpr) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracketKeyword("NULLIF", "(",
		p.commaSeparated(
			p.Doc(node.Expr1),
			p.Doc(node.Expr2),
		), ")", "")
}

func (node *PartitionBy) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// PARTITION BY NOTHING
	//
	// PARTITION BY LIST (...)
	//    ( ..values.. )
	//
	if node == nil {
		return pretty2.Keyword("PARTITION BY NOTHING")
	}

	var kw string
	if len(node.List) > 0 {
		kw = `PARTITION BY LIST`
	} else if len(node.Range) > 0 {
		kw = `PARTITION BY RANGE`
	}
	title := pretty2.ConcatSpace(pretty2.Keyword(kw),
		p.bracket("(", p.Doc(&node.Fields), ")"))

	inner := make([]pretty2.Doc, 0, len(node.List)+len(node.Range))
	for _, v := range node.List {
		inner = append(inner, p.Doc(&v))
	}
	for _, v := range node.Range {
		inner = append(inner, p.Doc(&v))
	}
	return p.nestUnder(title,
		p.bracket("(", p.commaSeparated(inner...), ")"),
	)
}

func (node *ListPartition) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// PARTITION name
	//   VALUES IN ( ... )
	//   [ .. subpartition ..]
	//
	title := pretty2.ConcatSpace(pretty2.Keyword("PARTITION"), p.Doc(&node.Name))

	clauses := make([]pretty2.Doc, 1, 2)
	clauses[0] = pretty2.ConcatSpace(
		pretty2.Keyword("VALUES IN"),
		p.bracket("(", p.Doc(&node.Exprs), ")"),
	)
	if node.Subpartition != nil {
		clauses = append(clauses, p.Doc(node.Subpartition))
	}
	return p.nestUnder(title, pretty2.Group(pretty2.Stack(clauses...)))
}

func (node *RangePartition) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// PARTITION name
	//   VALUES FROM (...)
	//   TO (...)
	//   [ .. subpartition ..]
	//
	title := pretty2.ConcatSpace(
		pretty2.Keyword("PARTITION"),
		p.Doc(&node.Name),
	)

	clauses := make([]pretty2.Doc, 2, 3)
	clauses[0] = pretty2.ConcatSpace(
		pretty2.Keyword("VALUES FROM"),
		p.bracket("(", p.Doc(&node.From), ")"))
	clauses[1] = pretty2.ConcatSpace(
		pretty2.Keyword("TO"),
		p.bracket("(", p.Doc(&node.To), ")"))

	if node.Subpartition != nil {
		clauses = append(clauses, p.Doc(node.Subpartition))
	}

	return p.nestUnder(title, pretty2.Group(pretty2.Stack(clauses...)))
}

func (node *ShardedIndexDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// USING HASH WITH BUCKET_COUNT = bucket_count
	//
	parts := []pretty2.Doc{
		pretty2.Keyword("USING HASH WITH BUCKET_COUNT = "),
		p.Doc(node.ShardBuckets),
	}
	return pretty2.Fold(pretty2.ConcatSpace, parts...)
}

func (node *InterleaveDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// INTERLEAVE IN PARENT tbl (...) [RESTRICT|CASCADE]
	//
	parts := []pretty2.Doc{
		pretty2.Keyword("INTERLEAVE IN PARENT"),
		p.Doc(&node.Parent),
		p.bracket("(", p.Doc(&node.Fields), ")"),
	}
	if node.DropBehavior != DropDefault {
		parts = append(parts, pretty2.Keyword(node.DropBehavior.String()))
	}
	return pretty2.Fold(pretty2.ConcatSpace, parts...)
}

func (node *CreateIndex) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	// CREATE [UNIQUE] [INVERTED] INDEX [name]
	//    ON tbl (cols...)
	//    [STORING ( ... )]
	//    [INTERLEAVE ...]
	//    [PARTITION BY ...]
	//
	title := make([]pretty2.Doc, 0, 6)
	title = append(title, pretty2.Keyword("CREATE"))
	if node.Unique {
		title = append(title, pretty2.Keyword("UNIQUE"))
	}
	if node.Inverted {
		title = append(title, pretty2.Keyword("INVERTED"))
	}
	title = append(title, pretty2.Keyword("INDEX"))
	if node.Concurrently {
		title = append(title, pretty2.Keyword("CONCURRENTLY"))
	}
	if node.IfNotExists {
		title = append(title, pretty2.Keyword("IF NOT EXISTS"))
	}
	if node.Name != "" {
		title = append(title, p.Doc(&node.Name))
	}

	clauses := make([]pretty2.Doc, 0, 5)
	clauses = append(clauses, pretty2.Fold(pretty2.ConcatSpace,
		pretty2.Keyword("ON"),
		p.Doc(&node.Table),
		p.bracket("(", p.Doc(&node.Columns), ")")))

	if node.Sharded != nil {
		clauses = append(clauses, p.Doc(node.Sharded))
	}
	if len(node.Storing) > 0 {
		clauses = append(clauses, p.bracketKeyword(
			"STORING", " (",
			p.Doc(&node.Storing),
			")", "",
		))
	}
	if node.Interleave != nil {
		clauses = append(clauses, p.Doc(node.Interleave))
	}
	if node.PartitionBy != nil {
		clauses = append(clauses, p.Doc(node.PartitionBy))
	}
	return p.nestUnder(
		pretty2.Fold(pretty2.ConcatSpace, title...),
		pretty2.Group(pretty2.Stack(clauses...)))
}

func (node *FamilyTableDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	// FAMILY [name] (columns...)
	//
	d := pretty2.Keyword("FAMILY")
	if node.Name != "" {
		d = pretty2.ConcatSpace(d, p.Doc(&node.Name))
	}
	return pretty2.ConcatSpace(d, p.bracket("(", p.Doc(&node.Columns), ")"))
}

func (node *IndexElem) doc(p *PrettyCfg) pretty2.Doc {
	d := p.Doc(&node.Column)
	if node.Direction != DefaultDirection {
		d = pretty2.ConcatSpace(d, pretty2.Keyword(node.Direction.String()))
	}
	if node.NullsOrder != DefaultNullsOrder {
		d = pretty2.ConcatSpace(d, pretty2.Keyword(node.NullsOrder.String()))
	}
	return d
}

func (node *IndexElemList) doc(p *PrettyCfg) pretty2.Doc {
	if node == nil || len(*node) == 0 {
		return pretty2.Nil
	}
	d := make([]pretty2.Doc, len(*node))
	for i := range *node {
		d[i] = p.Doc(&(*node)[i])
	}
	return p.commaSeparated(d...)
}

func (node *IndexTableDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	// [INVERTED] INDEX [name] (columns...)
	//    [STORING ( ... )]
	//    [INTERLEAVE ...]
	//    [PARTITION BY ...]
	//
	title := pretty2.Keyword("INDEX")
	if node.Name != "" {
		title = pretty2.ConcatSpace(title, p.Doc(&node.Name))
	}
	if node.Inverted {
		title = pretty2.ConcatSpace(pretty2.Keyword("INVERTED"), title)
	}
	title = pretty2.ConcatSpace(title, p.bracket("(", p.Doc(&node.Columns), ")"))

	clauses := make([]pretty2.Doc, 0, 4)
	if node.Sharded != nil {
		clauses = append(clauses, p.Doc(node.Sharded))
	}
	if node.Storing != nil {
		clauses = append(clauses, p.bracketKeyword(
			"STORING", "(",
			p.Doc(&node.Storing),
			")", ""))
	}
	if node.Interleave != nil {
		clauses = append(clauses, p.Doc(node.Interleave))
	}
	if node.PartitionBy != nil {
		clauses = append(clauses, p.Doc(node.PartitionBy))
	}

	if len(clauses) == 0 {
		return title
	}
	return p.nestUnder(title, pretty2.Group(pretty2.Stack(clauses...)))
}

func (node *UniqueConstraintTableDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	// [CONSTRAINT name]
	//    [PRIMARY KEY|UNIQUE] ( ... )
	//    [STORING ( ... )]
	//    [INTERLEAVE ...]
	//    [PARTITION BY ...]
	//
	// or (no constraint name):
	//
	// [PRIMARY KEY|UNIQUE] ( ... )
	//    [STORING ( ... )]
	//    [INTERLEAVE ...]
	//    [PARTITION BY ...]
	//
	clauses := make([]pretty2.Doc, 0, 5)
	var title pretty2.Doc
	if node.PrimaryKey {
		title = pretty2.Keyword("PRIMARY KEY")
	} else {
		title = pretty2.Keyword("UNIQUE")
	}
	title = pretty2.ConcatSpace(title, p.bracket("(", p.Doc(&node.Columns), ")"))
	if node.Name != "" {
		clauses = append(clauses, title)
		title = pretty2.ConcatSpace(pretty2.Keyword("CONSTRAINT"), p.Doc(&node.Name))
	}
	if node.Sharded != nil {
		clauses = append(clauses, p.Doc(node.Sharded))
	}
	if node.Storing != nil {
		clauses = append(clauses, p.bracketKeyword(
			"STORING", "(",
			p.Doc(&node.Storing),
			")", ""))
	}
	if node.Interleave != nil {
		clauses = append(clauses, p.Doc(node.Interleave))
	}
	if node.PartitionBy != nil {
		clauses = append(clauses, p.Doc(node.PartitionBy))
	}

	if len(clauses) == 0 {
		return title
	}
	return p.nestUnder(title, pretty2.Group(pretty2.Stack(clauses...)))
}

func (node *ForeignKeyConstraintTableDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	// [CONSTRAINT name]
	//    FOREIGN KEY (...)
	//    REFERENCES tbl (...)
	//    [MATCH ...]
	//    [ACTIONS ...]
	//
	// or (no constraint name):
	//
	// FOREIGN KEY (...)
	//    REFERENCES tbl [(...)]
	//    [MATCH ...]
	//    [ACTIONS ...]
	//
	clauses := make([]pretty2.Doc, 0, 4)
	title := pretty2.ConcatSpace(
		pretty2.Keyword("FOREIGN KEY"),
		p.bracket("(", p.Doc(&node.FromCols), ")"))

	if node.Name != "" {
		clauses = append(clauses, title)
		title = pretty2.ConcatSpace(pretty2.Keyword("CONSTRAINT"), p.Doc(&node.Name))
	}

	ref := pretty2.ConcatSpace(
		pretty2.Keyword("REFERENCES"), p.Doc(&node.Table))
	if len(node.ToCols) > 0 {
		ref = pretty2.ConcatSpace(ref, p.bracket("(", p.Doc(&node.ToCols), ")"))
	}
	clauses = append(clauses, ref)

	if node.Match != MatchSimple {
		clauses = append(clauses, pretty2.Keyword(node.Match.String()))
	}

	if actions := p.Doc(&node.Actions); ref != pretty2.Nil {
		clauses = append(clauses, actions)
	}

	return p.nestUnder(title, pretty2.Group(pretty2.Stack(clauses...)))
}

func (p *PrettyCfg) maybePrependConstraintName(constraintName *Name, d pretty2.Doc) pretty2.Doc {
	if *constraintName != "" {
		return pretty2.Fold(pretty2.ConcatSpace,
			pretty2.Keyword("CONSTRAINT"),
			p.Doc(constraintName),
			d)
	}
	return d
}

func (node *ColumnTableDef) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *ColumnTableDef) docRow(p *PrettyCfg) pretty2.TableRow {
	// Final layout:
	// colname
	//   type
	//   [AS ( ... ) STORED]
	//   [[CREATE [IF NOT EXISTS]] FAMILY [name]]
	//   [[CONSTRAINT name] DEFAULT expr]
	//   [[CONSTRAINT name] {NULL|NOT NULL}]
	//   [[CONSTRAINT name] {PRIMARY KEY|UNIQUE}]
	//   [[CONSTRAINT name] CHECK ...]
	//   [[CONSTRAINT name] REFERENCES tbl (...)
	//         [MATCH ...]
	//         [ACTIONS ...]
	//   ]
	//
	clauses := make([]pretty2.Doc, 0, 7)

	// Column type.
	// ColumnTableDef node type will not be specified if it represents a CREATE
	// TABLE ... AS query.
	if node.Type != nil {
		clauses = append(clauses, pretty2.Text(node.columnTypeString()))
	}

	// Compute expression (for computed columns).
	if node.IsComputed() {
		clauses = append(clauses, pretty2.ConcatSpace(pretty2.Keyword("AS"),
			p.bracket("(", p.Doc(node.Computed.Expr), ") STORED"),
		))
	}

	// Column family.
	if node.HasColumnFamily() {
		d := pretty2.Keyword("FAMILY")
		if node.Family.Name != "" {
			d = pretty2.ConcatSpace(d, p.Doc(&node.Family.Name))
		}
		if node.Family.Create {
			c := pretty2.Keyword("CREATE")
			if node.Family.IfNotExists {
				c = pretty2.ConcatSpace(c, pretty2.Keyword("IF NOT EXISTS"))
			}
			d = pretty2.ConcatSpace(c, d)
		}
		clauses = append(clauses, d)
	}

	// DEFAULT constraint.
	if node.HasDefaultExpr() {
		clauses = append(clauses, p.maybePrependConstraintName(&node.DefaultExpr.ConstraintName,
			pretty2.ConcatSpace(pretty2.Keyword("DEFAULT"), p.Doc(node.DefaultExpr.Expr))))
	}

	// NULL/NOT NULL constraint.
	nConstraint := pretty2.Nil
	switch node.Nullable.Nullability {
	case Null:
		nConstraint = pretty2.Keyword("NULL")
	case NotNull:
		nConstraint = pretty2.Keyword("NOT NULL")
	}
	if nConstraint != pretty2.Nil {
		clauses = append(clauses, p.maybePrependConstraintName(&node.Nullable.ConstraintName, nConstraint))
	}

	// PRIMARY KEY / UNIQUE constraint.
	pkConstraint := pretty2.Nil
	if node.PrimaryKey.IsPrimaryKey {
		pkConstraint = pretty2.Keyword("PRIMARY KEY")
	} else if node.Unique {
		pkConstraint = pretty2.Keyword("UNIQUE")
	}
	if pkConstraint != pretty2.Nil {
		clauses = append(clauses, p.maybePrependConstraintName(&node.UniqueConstraintName, pkConstraint))
	}

	if node.PrimaryKey.Sharded {
		clauses = append(clauses, pretty2.Keyword("USING HASH WITH BUCKET_COUNT = "))
		clauses = append(clauses, p.Doc(node.PrimaryKey.ShardBuckets))
	}
	// CHECK expressions/constraints.
	for _, checkExpr := range node.CheckExprs {
		clauses = append(clauses, p.maybePrependConstraintName(&checkExpr.ConstraintName,
			pretty2.ConcatSpace(pretty2.Keyword("CHECK"), p.bracket("(", p.Doc(checkExpr.Expr), ")"))))
	}

	// FK constraints.
	if node.HasFKConstraint() {
		fkHead := pretty2.ConcatSpace(pretty2.Keyword("REFERENCES"), p.Doc(node.References.Table))
		if node.References.Col != "" {
			fkHead = pretty2.ConcatSpace(fkHead, p.bracket("(", p.Doc(&node.References.Col), ")"))
		}
		fkDetails := make([]pretty2.Doc, 0, 2)
		// We omit MATCH SIMPLE because it is the default.
		if node.References.Match != MatchSimple {
			fkDetails = append(fkDetails, pretty2.Keyword(node.References.Match.String()))
		}
		if ref := p.Doc(&node.References.Actions); ref != pretty2.Nil {
			fkDetails = append(fkDetails, ref)
		}
		fk := fkHead
		if len(fkDetails) > 0 {
			fk = p.nestUnder(fk, pretty2.Group(pretty2.Stack(fkDetails...)))
		}
		clauses = append(clauses, p.maybePrependConstraintName(&node.References.ConstraintName, fk))
	}

	// Prevents an additional space from being appended at the end of every column
	// name in the case of CREATE TABLE ... AS query. The additional space is
	// being caused due to the absence of column type qualifiers in CTAS queries.
	//
	// TODO(adityamaru): Consult someone with more knowledge about the pretty
	// printer architecture to find a cleaner solution.
	var tblRow pretty2.TableRow
	if node.Type == nil {
		tblRow = pretty2.TableRow{
			Label: node.Name.String(),
			Doc:   pretty2.Stack(clauses...),
		}
	} else {
		tblRow = pretty2.TableRow{
			Label: node.Name.String(),
			Doc:   pretty2.Group(pretty2.Stack(clauses...)),
		}
	}

	return tblRow
}

func (node *CheckConstraintTableDef) doc(p *PrettyCfg) pretty2.Doc {
	// Final layout:
	//
	// CONSTRAINT name
	//    CHECK (...)
	//
	// or (no constraint name):
	//
	// CHECK (...)
	//
	d := pretty2.ConcatSpace(pretty2.Keyword("CHECK"),
		p.bracket("(", p.Doc(node.Expr), ")"))

	if node.Name != "" {
		d = p.nestUnder(
			pretty2.ConcatSpace(
				pretty2.Keyword("CONSTRAINT"),
				p.Doc(&node.Name),
			),
			d,
		)
	}
	return d
}

func (node *ReferenceActions) doc(p *PrettyCfg) pretty2.Doc {
	var docs []pretty2.Doc
	if node.Delete != NoAction {
		docs = append(docs,
			pretty2.Keyword("ON DELETE"),
			pretty2.Keyword(node.Delete.String()),
		)
	}
	if node.Update != NoAction {
		docs = append(docs,
			pretty2.Keyword("ON UPDATE"),
			pretty2.Keyword(node.Update.String()),
		)
	}
	return pretty2.Fold(pretty2.ConcatSpace, docs...)
}

func (node *Backup) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 0, 6)

	items = append(items, p.row("BACKUP", pretty2.Nil))
	if node.DescriptorCoverage == RequestedDescriptors {
		items = append(items, node.Targets.docRow(p))
	}
	items = append(items, p.row("TO", p.Doc(&node.To)))

	if node.AsOf.Expr != nil {
		items = append(items, node.AsOf.docRow(p))
	}
	if node.IncrementalFrom != nil {
		items = append(items, p.row("INCREMENTAL FROM", p.Doc(&node.IncrementalFrom)))
	}
	if node.Options != nil {
		items = append(items, p.row("WITH", p.Doc(&node.Options)))
	}
	return p.rlTable(items...)
}

func (node *Restore) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 0, 5)

	items = append(items, p.row("RESTORE", pretty2.Nil))
	if node.DescriptorCoverage == RequestedDescriptors {
		items = append(items, node.Targets.docRow(p))
	}
	from := make([]pretty2.Doc, len(node.From))
	for i := range node.From {
		from[i] = p.Doc(&node.From[i])
	}
	items = append(items, p.row("FROM", p.commaSeparated(from...)))

	if node.AsOf.Expr != nil {
		items = append(items, node.AsOf.docRow(p))
	}
	if node.Options != nil {
		items = append(items, p.row("WITH", p.Doc(&node.Options)))
	}
	return p.rlTable(items...)
}

func (node *TargetList) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *TargetList) docRow(p *PrettyCfg) pretty2.TableRow {
	if node.Databases != nil {
		return p.row("DATABASE", p.Doc(&node.Databases))
	}
	return p.row("TABLE", p.Doc(&node.Tables))
}

func (node *AsOfClause) doc(p *PrettyCfg) pretty2.Doc {
	return p.unrow(node.docRow(p))
}

func (node *AsOfClause) docRow(p *PrettyCfg) pretty2.TableRow {
	return p.row("AS OF SYSTEM TIME", p.Doc(node.Expr))
}

func (node *KVOptions) doc(p *PrettyCfg) pretty2.Doc {
	var opts []pretty2.Doc
	for _, opt := range *node {
		d := p.Doc(&opt.Key)
		if opt.Value != nil {
			d = pretty2.Fold(pretty2.ConcatSpace,
				d,
				pretty2.Text("="),
				p.Doc(opt.Value),
			)
		}
		opts = append(opts, d)
	}
	return p.commaSeparated(opts...)
}

func (node *Import) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 0, 5)
	items = append(items, p.row("IMPORT", pretty2.Nil))

	if node.Bundle {
		if node.Table != nil {
			items = append(items, p.row("TABLE", p.Doc(node.Table)))
			items = append(items, p.row("FROM", pretty2.Nil))
		}
		items = append(items, p.row(node.FileFormat, p.Doc(&node.Files)))
	} else {
		if node.Into {
			into := p.Doc(node.Table)
			if node.IntoCols != nil {
				into = p.nestUnder(into, p.bracket("(", p.Doc(&node.IntoCols), ")"))
			}
			items = append(items, p.row("INTO", into))
		} else {
			if node.CreateFile != nil {
				items = append(items, p.row("TABLE", p.Doc(node.Table)))
				items = append(items, p.row("CREATE USING", p.Doc(node.CreateFile)))
			} else {
				table := p.bracketDoc(
					pretty2.ConcatSpace(p.Doc(node.Table), pretty2.Text("(")),
					p.Doc(&node.CreateDefs),
					pretty2.Text(")"),
				)
				items = append(items, p.row("TABLE", table))
			}
		}

		data := p.bracketKeyword(
			"DATA", " (",
			p.Doc(&node.Files),
			")", "",
		)
		items = append(items, p.row(node.FileFormat, data))
	}
	if node.Options != nil {
		items = append(items, p.row("WITH", p.Doc(&node.Options)))
	}
	return p.rlTable(items...)
}

func (node *Export) doc(p *PrettyCfg) pretty2.Doc {
	items := make([]pretty2.TableRow, 0, 5)
	items = append(items, p.row("EXPORT", pretty2.Nil))
	items = append(items, p.row("INTO "+node.FileFormat, p.Doc(node.File)))
	if node.Options != nil {
		items = append(items, p.row("WITH", p.Doc(&node.Options)))
	}
	items = append(items, p.row("FROM", p.Doc(node.Query)))
	return p.rlTable(items...)
}

func (node *Explain) doc(p *PrettyCfg) pretty2.Doc {
	d := pretty2.Keyword("EXPLAIN")
	showMode := node.Mode != ExplainPlan
	// ANALYZE is a special case because it is a statement implemented as an
	// option to EXPLAIN.
	if node.Flags[ExplainFlagAnalyze] {
		d = pretty2.ConcatSpace(d, pretty2.Keyword("ANALYZE"))
		showMode = true
	}
	var opts []pretty2.Doc
	if showMode {
		opts = append(opts, pretty2.Keyword(node.Mode.String()))
	}
	for f := ExplainFlag(1); f <= numExplainFlags; f++ {
		if f != ExplainFlagAnalyze && node.Flags[f] {
			opts = append(opts, pretty2.Keyword(f.String()))
		}
	}
	if len(opts) > 0 {
		d = pretty2.ConcatSpace(
			d,
			p.bracket("(", p.commaSeparated(opts...), ")"),
		)
	}
	return p.nestUnder(d, p.Doc(node.Statement))
}

func (node *ExplainAnalyzeDebug) doc(p *PrettyCfg) pretty2.Doc {
	d := pretty2.ConcatSpace(
		pretty2.ConcatSpace(
			pretty2.Keyword("EXPLAIN"),
			pretty2.Keyword("ANALYZE"),
		),
		p.bracket("(", pretty2.Keyword("DEBUG"), ")"),
	)
	return p.nestUnder(d, p.Doc(node.Statement))
}

func (node *NotExpr) doc(p *PrettyCfg) pretty2.Doc {
	return p.nestUnder(
		pretty2.Keyword("NOT"),
		p.exprDocWithParen(node.Expr),
	)
}

func (node *CoalesceExpr) doc(p *PrettyCfg) pretty2.Doc {
	return p.bracketKeyword(
		node.Name, "(",
		p.Doc(&node.Exprs),
		")", "",
	)
}

func (node *AlterTable) doc(p *PrettyCfg) pretty2.Doc {
	title := pretty2.Keyword("ALTER TABLE")
	if node.IfExists {
		title = pretty2.ConcatSpace(title, pretty2.Keyword("IF EXISTS"))
	}
	title = pretty2.ConcatSpace(title, p.Doc(node.Table))
	return p.nestUnder(
		title,
		p.Doc(&node.Cmds),
	)
}

func (node *AlterTableCmds) doc(p *PrettyCfg) pretty2.Doc {
	cmds := make([]pretty2.Doc, len(*node))
	for i, c := range *node {
		cmds[i] = p.Doc(c)
	}
	return p.commaSeparated(cmds...)
}

func (node *AlterTableAddColumn) doc(p *PrettyCfg) pretty2.Doc {
	title := pretty2.Keyword("ADD COLUMN")
	if node.IfNotExists {
		title = pretty2.ConcatSpace(title, pretty2.Keyword("IF NOT EXISTS"))
	}
	return p.nestUnder(
		title,
		p.Doc(node.ColumnDef),
	)
}

func (node *Prepare) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *Prepare) docTable(p *PrettyCfg) []pretty2.TableRow {
	name := p.Doc(&node.Name)
	if len(node.Types) > 0 {
		typs := make([]pretty2.Doc, len(node.Types))
		for i, t := range node.Types {
			typs[i] = pretty2.Text(t.SQLString())
		}
		name = pretty2.ConcatSpace(name,
			p.bracket("(", p.commaSeparated(typs...), ")"),
		)
	}
	return []pretty2.TableRow{
		p.row("PREPARE", name),
		p.row("AS", p.Doc(node.Statement)),
	}
}

func (node *Execute) doc(p *PrettyCfg) pretty2.Doc {
	return p.rlTable(node.docTable(p)...)
}

func (node *Execute) docTable(p *PrettyCfg) []pretty2.TableRow {
	name := p.Doc(&node.Name)
	if len(node.Params) > 0 {
		name = pretty2.ConcatSpace(
			name,
			p.bracket("(", p.Doc(&node.Params), ")"),
		)
	}
	rows := []pretty2.TableRow{p.row("EXECUTE", name)}
	if node.DiscardRows {
		rows = append(rows, p.row("", pretty2.Keyword("DISCARD ROWS")))
	}
	return rows
}

func (node *AnnotateTypeExpr) doc(p *PrettyCfg) pretty2.Doc {
	if node.SyntaxMode == AnnotateShort {
		switch node.Type.Family() {
		case types2.JsonFamily:
			if sv, ok := node.Expr.(*StrVal); ok && p.JSONFmt {
				return p.jsonCast(sv, ":::", node.Type)
			}
		}
	}
	return p.docAsString(node)
}

// jsonCast attempts to pretty print a string that is cast or asserted as JSON.
func (p *PrettyCfg) jsonCast(sv *StrVal, op string, typ *types2.T) pretty2.Doc {
	return pretty2.Fold(pretty2.Concat,
		p.jsonString(sv.RawString()),
		pretty2.Text(op),
		pretty2.Text(typ.SQLString()),
	)
}

// jsonString parses s as JSON and pretty prints it.
func (p *PrettyCfg) jsonString(s string) pretty2.Doc {
	j, err := json.ParseJSON(s)
	if err != nil {
		return pretty2.Text(s)
	}
	return p.bracket(`'`, p.jsonNode(j), `'`)
}

// jsonNode pretty prints a JSON node.
func (p *PrettyCfg) jsonNode(j json.JSON) pretty2.Doc {
	// Figure out what type this is.
	if it, _ := j.ObjectIter(); it != nil {
		// Object.
		elems := make([]pretty2.Doc, 0, j.Len())
		for it.Next() {
			elems = append(elems, p.nestUnder(
				pretty2.Concat(
					pretty2.Text(json.FromString(it.Key()).String()),
					pretty2.Text(`:`),
				),
				p.jsonNode(it.Value()),
			))
		}
		return p.bracket("{", p.commaSeparated(elems...), "}")
	} else if n := j.Len(); n > 0 {
		// Non-empty array.
		elems := make([]pretty2.Doc, n)
		for i := 0; i < n; i++ {
			elem, err := j.FetchValIdx(i)
			if err != nil {
				return pretty2.Text(j.String())
			}
			elems[i] = p.jsonNode(elem)
		}
		return p.bracket("[", p.commaSeparated(elems...), "]")
	}
	// Other.
	return pretty2.Text(j.String())
}
