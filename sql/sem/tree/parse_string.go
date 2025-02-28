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
	"github.com/cockroachdb/errors"
	types2 "github.com/iota-uz/psql-parser/sql/types"
	"github.com/iota-uz/psql-parser/util"
)

// ParseAndRequireString parses s as type t for simple types. Arrays and collated
// strings are not handled.
func ParseAndRequireString(t *types2.T, s string, ctx ParseTimeContext) (Datum, error) {
	switch t.Family() {
	case types2.ArrayFamily:
		return ParseDArrayFromString(ctx, s, t.ArrayContents())
	case types2.BitFamily:
		return ParseDBitArray(s)
	case types2.BoolFamily:
		return ParseDBool(s)
	case types2.BytesFamily:
		return ParseDByte(s)
	case types2.DateFamily:
		return ParseDDate(ctx, s)
	case types2.DecimalFamily:
		return ParseDDecimal(s)
	case types2.FloatFamily:
		return ParseDFloat(s)
	case types2.INetFamily:
		return ParseDIPAddrFromINetString(s)
	case types2.IntFamily:
		return ParseDInt(s)
	case types2.IntervalFamily:
		itm, err := t.IntervalTypeMetadata()
		if err != nil {
			return nil, err
		}
		return ParseDIntervalWithTypeMetadata(s, itm)
	case types2.JsonFamily:
		return ParseDJSON(s)
	case types2.OidFamily:
		i, err := ParseDInt(s)
		return NewDOid(*i), err
	case types2.StringFamily:
		// If the string type specifies a limit we truncate to that limit:
		//   'hello'::CHAR(2) -> 'he'
		// This is true of all the string type variants.
		if t.Width() > 0 {
			s = util.TruncateString(s, int(t.Width()))
		}
		return NewDString(s), nil
	case types2.TimeFamily:
		return ParseDTime(ctx, s, TimeFamilyPrecisionToRoundDuration(t.Precision()))
	case types2.TimeTZFamily:
		return ParseDTimeTZ(ctx, s, TimeFamilyPrecisionToRoundDuration(t.Precision()))
	case types2.TimestampFamily:
		return ParseDTimestamp(ctx, s, TimeFamilyPrecisionToRoundDuration(t.Precision()))
	case types2.TimestampTZFamily:
		return ParseDTimestampTZ(ctx, s, TimeFamilyPrecisionToRoundDuration(t.Precision()))
	case types2.UuidFamily:
		return ParseDUuidFromString(s)
	default:
		return nil, errors.AssertionFailedf("unknown type %s (%T)", t, t)
	}
}
