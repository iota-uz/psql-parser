// Copyright 2019 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

//go:build gofuzz
// +build gofuzz

package tree

import (
	"github.com/iota-uz/psql-parser/util/timeutil"
)

var (
	timeCtx = NewParseTimeContext(timeutil.Now())
)

func FuzzParseDDecimal(data []byte) int {
	_, err := ParseDDecimal(string(data))
	if err != nil {
		return 0
	}
	return 1
}

func FuzzParseDDate(data []byte) int {
	_, err := ParseDDate(timeCtx, string(data))
	if err != nil {
		return 0
	}
	return 1
}
