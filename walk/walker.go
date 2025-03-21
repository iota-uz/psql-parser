package walk

import (
	"fmt"
	"github.com/iota-uz/psql-parser/sql/parser"
	tree2 "github.com/iota-uz/psql-parser/sql/sem/tree"
	"github.com/iota-uz/psql-parser/util/set"
	"log"
	"strings"
)

type AstWalker struct {
	UnknownNodes []interface{}
	Fn           func(ctx interface{}, node interface{}) (stop bool)
}
type ReferredCols map[string]int

func (rc ReferredCols) ToList() []string {
	cols := make([]string, len(rc))
	i := 0
	for k := range rc {
		cols[i] = k
		i++
	}
	return set.SortDeDup(cols)
}

func (w *AstWalker) Walk(stmts parser.Statements, ctx interface{}) (ok bool, err error) {

	w.UnknownNodes = make([]interface{}, 0)
	asts := make([]tree2.NodeFormatter, len(stmts))
	for si, stmt := range stmts {
		asts[si] = stmt.AST
	}

	// nodeCount is incremented on each visited node per statement. It is
	// currently used to determine if walk is at the top-level statement
	// or not.
	var walk func(...interface{})
	walk = func(nodes ...interface{}) {
		for _, node := range nodes {
			if w.Fn != nil {
				if w.Fn(ctx, node) {
					break
				}
			}

			if node == nil {
				continue
			}
			if _, ok := node.(tree2.Datum); ok {
				continue
			}

			switch node := node.(type) {
			case *tree2.AliasedTableExpr:
				walk(node.Expr)
			case *tree2.AndExpr:
				walk(node.Left, node.Right)
			case *tree2.AnnotateTypeExpr:
				walk(node.Expr)
			case *tree2.Array:
				walk(node.Exprs)
			case tree2.AsOfClause:
				walk(node.Expr)
			case *tree2.BinaryExpr:
				walk(node.Left, node.Right)
			case *tree2.CaseExpr:
				walk(node.Expr, node.Else)
				for _, when := range node.Whens {
					walk(when.Cond, when.Val)
				}
			case *tree2.RangeCond:
				walk(node.Left, node.From, node.To)
			case *tree2.CastExpr:
				walk(node.Expr)
			case *tree2.CoalesceExpr:
				for _, expr := range node.Exprs {
					walk(expr)
				}
			case *tree2.ColumnTableDef:
			case *tree2.ComparisonExpr:
				walk(node.Left, node.Right)
			case *tree2.CreateTable:
				for _, def := range node.Defs {
					walk(def)
				}
				if node.AsSource != nil {
					walk(node.AsSource)
				}
			case *tree2.CTE:
				walk(node.Stmt)
			case *tree2.DBool:
			case tree2.Exprs:
				for _, expr := range node {
					walk(expr)
				}
			case *tree2.FamilyTableDef:
			case *tree2.From:
				walk(node.AsOf)
				for _, table := range node.Tables {
					walk(table)
				}
			case *tree2.FuncExpr:
				if node.WindowDef != nil {
					walk(node.WindowDef)
				}
				walk(node.Exprs, node.Filter)
			case *tree2.IndexTableDef:
			case *tree2.JoinTableExpr:
				walk(node.Left, node.Right, node.Cond)
			case *tree2.NotExpr:
				walk(node.Expr)
			case *tree2.NumVal:
			case *tree2.OnJoinCond:
				walk(node.Expr)
			case *tree2.Order:
				walk(node.Expr, node.Table)
			case tree2.OrderBy:
				for _, order := range node {
					walk(order)
				}
			case *tree2.OrExpr:
				walk(node.Left, node.Right)
			case *tree2.ParenExpr:
				walk(node.Expr)
			case *tree2.ParenSelect:
				walk(node.Select)
			case *tree2.RowsFromExpr:
				for _, expr := range node.Items {
					walk(expr)
				}
			case *tree2.Select:
				if node.With != nil {
					walk(node.With)
				}
				if node.OrderBy != nil {
					walk(node.OrderBy)
				}
				if node.Limit != nil {
					walk(node.Limit)
				}
				walk(node.Select)
			case *tree2.Limit:
				walk(node.Count)
			case *tree2.SelectClause:
				walk(node.Exprs)
				if node.Where != nil {
					walk(node.Where)
				}
				if node.Having != nil {
					walk(node.Having)
				}
				if node.DistinctOn != nil {
					for _, distinct := range node.DistinctOn {
						walk(distinct)
					}
				}
				if node.GroupBy != nil {
					for _, group := range node.GroupBy {
						walk(group)
					}
				}
				walk(&node.From)
			case tree2.SelectExpr:
				walk(node.Expr)
			case tree2.SelectExprs:
				for _, expr := range node {
					walk(expr)
				}
			case *tree2.SetVar:
				for _, expr := range node.Values {
					walk(expr)
				}
			case *tree2.StrVal:
			case *tree2.Subquery:
				walk(node.Select)
			case tree2.TableExprs:
				for _, expr := range node {
					walk(expr)
				}
			case *tree2.TableName, tree2.TableName:
			case *tree2.Tuple:
				for _, expr := range node.Exprs {
					walk(expr)
				}
			case *tree2.UnaryExpr:
				walk(node.Expr)
			case *tree2.UniqueConstraintTableDef:
			case *tree2.UnionClause:
				walk(node.Left, node.Right)
			case tree2.UnqualifiedStar:
			case *tree2.UnresolvedName:
			case *tree2.ValuesClause:
				for _, row := range node.Rows {
					walk(row)
				}
			case *tree2.Where:
				walk(node.Expr)
			case tree2.Window:
				for _, windowDef := range node {
					walk(windowDef)
				}
			case *tree2.WindowDef:
				walk(node.Partitions)
				if node.Frame != nil {
					walk(node.Frame)
				}
			case *tree2.WindowFrame:
				if node.Bounds.StartBound != nil {
					walk(node.Bounds.StartBound)
				}
				if node.Bounds.EndBound != nil {
					walk(node.Bounds.EndBound)
				}
			case *tree2.WindowFrameBound:
				walk(node.OffsetExpr)
			case *tree2.With:
				for _, expr := range node.CTEList {
					walk(expr)
				}
			default:
				if w.UnknownNodes != nil {
					w.UnknownNodes = append(w.UnknownNodes, node)
				}
			}
		}
	}

	for _, ast := range asts {
		walk(ast)
	}

	return true, nil
}

func isColumn(node interface{}) bool {
	switch node.(type) {
	// it's wired that the "Subquery" type is also "VariableExpr" type
	// we have to ignore that case.
	case *tree2.Subquery:
		return false
	case tree2.VariableExpr:
		return true
	}
	return false
}

// ColNamesInSelect finds all referred variables in a Select Statement.
// (variables = sub-expressions, placeholders, indexed vars, etc.)
// Implementation limits:
//  1. Table with AS is not normalized.
//  2. Columns referred from outer query are not translated.
func ColNamesInSelect(sql string) (referredCols ReferredCols, err error) {
	referredCols = make(ReferredCols, 0)

	w := &AstWalker{
		Fn: func(ctx interface{}, node interface{}) (stop bool) {
			rCols := ctx.(ReferredCols)
			if isColumn(node) {
				nodeName := fmt.Sprint(node)
				// just drop the "table." part
				tableCols := strings.Split(nodeName, ".")
				colName := tableCols[len(tableCols)-1]
				rCols[colName] = 1
			}
			return false
		},
	}
	stmts, err := parser.Parse(sql)
	if err != nil {
		return
	}

	_, err = w.Walk(stmts, referredCols)
	if err != nil {
		return
	}
	for _, col := range w.UnknownNodes {
		log.Printf("unhandled column type %T", col)
	}
	return
}

func AllColsContained(set ReferredCols, cols []string) bool {
	if cols == nil {
		if set == nil {
			return true
		} else {
			return false
		}
	}
	if len(set) != len(cols) {
		return false
	}
	for _, col := range cols {
		if _, exist := set[col]; !exist {
			return false
		}
	}
	return true
}
