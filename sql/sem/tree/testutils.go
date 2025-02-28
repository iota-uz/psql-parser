// Copyright 2017 The Cockroach Authors.
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
	"fmt"
	types2 "github.com/iota-uz/psql-parser/sql/types"
	"github.com/iota-uz/psql-parser/util/timeofday"
	"github.com/iota-uz/psql-parser/util/timeutil"
	"github.com/iota-uz/psql-parser/util/timeutil/pgdate"
	"time"
)

// presetTypesForTesting is a mapping of qualified names to types that can be mocked out
// for tests to allow the qualified names to be type checked without throwing an error.
var presetTypesForTesting map[string]*types2.T

// MockNameTypes populates presetTypesForTesting for a test.
func MockNameTypes(types map[string]*types2.T) func() {
	presetTypesForTesting = types
	return func() {
		presetTypesForTesting = nil
	}
}

// SampleDatum is intended to be a more lightweight version of RandDatum for
// when you just need one consistent example of a datum.
func SampleDatum(t *types2.T) Datum {
	switch t.Family() {
	case types2.BitFamily:
		a, _ := NewDBitArrayFromInt(123, 40)
		return a
	case types2.BoolFamily:
		return MakeDBool(true)
	case types2.IntFamily:
		return NewDInt(123)
	case types2.FloatFamily:
		f := DFloat(123.456)
		return &f
	case types2.DecimalFamily:
		d := &DDecimal{}
		// int64(rng.Uint64()) to get negative numbers, too
		d.Decimal.SetFinite(3, 6)
		return d
	case types2.StringFamily:
		return NewDString("Carl")
	case types2.BytesFamily:
		return NewDBytes("Princess")
	case types2.DateFamily:
		return NewDDate(pgdate.MakeCompatibleDateFromDisk(123123))
	case types2.TimeFamily:
		return MakeDTime(timeofday.FromInt(789))
	case types2.TimeTZFamily:
		return NewDTimeTZFromOffset(timeofday.FromInt(345), 5*60*60 /* OffsetSecs */)
	case types2.TimestampFamily:
		return MakeDTimestamp(timeutil.Unix(123, 123), time.Second)
	case types2.TimestampTZFamily:
		return MakeDTimestampTZ(timeutil.Unix(123, 123), time.Second)
	case types2.IntervalFamily:
		i, _ := ParseDInterval("1h1m1s")
		return i
	case types2.UuidFamily:
		u, _ := ParseDUuidFromString("3189ad07-52f2-4d60-83e8-4a8347fef718")
		return u
	case types2.INetFamily:
		i, _ := ParseDIPAddrFromINetString("127.0.0.1")
		return i
	case types2.JsonFamily:
		j, _ := ParseDJSON(`{"a": "b"}`)
		return j
	case types2.OidFamily:
		return NewDOid(DInt(1009))
	default:
		panic(fmt.Sprintf("SampleDatum not implemented for %s", t))
	}
}
