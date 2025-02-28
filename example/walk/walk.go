package main

import (
	"github.com/iota-uz/psql-parser/sql/parser"
	"github.com/iota-uz/psql-parser/walk"
	"log"
)

func main() {
	sql := `select marr
			from (select marr_stat_cd AS marr, label AS l
				  from root_loan_mock_v4
				  order by root_loan_mock_v4.age desc, l desc
				  limit 5) as v4
			LIMIT 1;`
	w := &walk.AstWalker{
		Fn: func(ctx interface{}, node interface{}) (stop bool) {
			log.Printf("node type %T", node)
			return false
		},
	}
	stmts, err := parser.Parse(sql)
	if err != nil {
		return
	}

	_, _ = w.Walk(stmts, nil)
	return
}
