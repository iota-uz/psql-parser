// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: util/protoutil/clone.proto

package protoutil

import (
	github_com_cockroachdb_cockroach_pkg_util_uuid "github.com/iota-uz/psql-parser/util/uuid"
	proto "github.com/gogo/protobuf/proto"
)
import fmt "fmt"
import math "math"

import io "io"

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.GoGoProtoPackageIsVersion2 // please upgrade the proto package

type RecursiveAndUncloneable struct {
	R    *RecursiveAndUncloneable                            `protobuf:"bytes,1,opt,name=r,proto3" json:"r,omitempty"`
	Uuid github_com_cockroachdb_cockroach_pkg_util_uuid.UUID `protobuf:"bytes,2,opt,name=uuid,proto3,customtype=github.com/iota-uz/psql-parser/pkg/util/uuid.UUID" json:"uuid"`
}

func (m *RecursiveAndUncloneable) Reset()         { *m = RecursiveAndUncloneable{} }
func (m *RecursiveAndUncloneable) String() string { return proto.CompactTextString(m) }
func (*RecursiveAndUncloneable) ProtoMessage()    {}
func (*RecursiveAndUncloneable) Descriptor() ([]byte, []int) {
	return fileDescriptor_clone_96c900215ff8e4e9, []int{0}
}
func (m *RecursiveAndUncloneable) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *RecursiveAndUncloneable) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	b = b[:cap(b)]
	n, err := m.MarshalTo(b)
	if err != nil {
		return nil, err
	}
	return b[:n], nil
}
func (dst *RecursiveAndUncloneable) XXX_Merge(src proto.Message) {
	xxx_messageInfo_RecursiveAndUncloneable.Merge(dst, src)
}
func (m *RecursiveAndUncloneable) XXX_Size() int {
	return m.Size()
}
func (m *RecursiveAndUncloneable) XXX_DiscardUnknown() {
	xxx_messageInfo_RecursiveAndUncloneable.DiscardUnknown(m)
}

var xxx_messageInfo_RecursiveAndUncloneable proto.InternalMessageInfo

func init() {
	proto.RegisterType((*RecursiveAndUncloneable)(nil), "cockroach.util.protoutil.RecursiveAndUncloneable")
}
func (m *RecursiveAndUncloneable) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalTo(dAtA)
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *RecursiveAndUncloneable) MarshalTo(dAtA []byte) (int, error) {
	var i int
	_ = i
	var l int
	_ = l
	if m.R != nil {
		dAtA[i] = 0xa
		i++
		i = encodeVarintClone(dAtA, i, uint64(m.R.Size()))
		n1, err := m.R.MarshalTo(dAtA[i:])
		if err != nil {
			return 0, err
		}
		i += n1
	}
	dAtA[i] = 0x12
	i++
	i = encodeVarintClone(dAtA, i, uint64(m.Uuid.Size()))
	n2, err := m.Uuid.MarshalTo(dAtA[i:])
	if err != nil {
		return 0, err
	}
	i += n2
	return i, nil
}

func encodeVarintClone(dAtA []byte, offset int, v uint64) int {
	for v >= 1<<7 {
		dAtA[offset] = uint8(v&0x7f | 0x80)
		v >>= 7
		offset++
	}
	dAtA[offset] = uint8(v)
	return offset + 1
}
func (m *RecursiveAndUncloneable) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.R != nil {
		l = m.R.Size()
		n += 1 + l + sovClone(uint64(l))
	}
	l = m.Uuid.Size()
	n += 1 + l + sovClone(uint64(l))
	return n
}

func sovClone(x uint64) (n int) {
	for {
		n++
		x >>= 7
		if x == 0 {
			break
		}
	}
	return n
}
func sozClone(x uint64) (n int) {
	return sovClone(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *RecursiveAndUncloneable) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowClone
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= (uint64(b) & 0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: RecursiveAndUncloneable: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: RecursiveAndUncloneable: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field R", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowClone
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= (int(b) & 0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthClone
			}
			postIndex := iNdEx + msglen
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.R == nil {
				m.R = &RecursiveAndUncloneable{}
			}
			if err := m.R.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Uuid", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowClone
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				byteLen |= (int(b) & 0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if byteLen < 0 {
				return ErrInvalidLengthClone
			}
			postIndex := iNdEx + byteLen
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if err := m.Uuid.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipClone(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthClone
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func skipClone(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowClone
			}
			if iNdEx >= l {
				return 0, io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= (uint64(b) & 0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		wireType := int(wire & 0x7)
		switch wireType {
		case 0:
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return 0, ErrIntOverflowClone
				}
				if iNdEx >= l {
					return 0, io.ErrUnexpectedEOF
				}
				iNdEx++
				if dAtA[iNdEx-1] < 0x80 {
					break
				}
			}
			return iNdEx, nil
		case 1:
			iNdEx += 8
			return iNdEx, nil
		case 2:
			var length int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return 0, ErrIntOverflowClone
				}
				if iNdEx >= l {
					return 0, io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				length |= (int(b) & 0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			iNdEx += length
			if length < 0 {
				return 0, ErrInvalidLengthClone
			}
			return iNdEx, nil
		case 3:
			for {
				var innerWire uint64
				var start int = iNdEx
				for shift := uint(0); ; shift += 7 {
					if shift >= 64 {
						return 0, ErrIntOverflowClone
					}
					if iNdEx >= l {
						return 0, io.ErrUnexpectedEOF
					}
					b := dAtA[iNdEx]
					iNdEx++
					innerWire |= (uint64(b) & 0x7F) << shift
					if b < 0x80 {
						break
					}
				}
				innerWireType := int(innerWire & 0x7)
				if innerWireType == 4 {
					break
				}
				next, err := skipClone(dAtA[start:])
				if err != nil {
					return 0, err
				}
				iNdEx = start + next
			}
			return iNdEx, nil
		case 4:
			return iNdEx, nil
		case 5:
			iNdEx += 4
			return iNdEx, nil
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
	}
	panic("unreachable")
}

var (
	ErrInvalidLengthClone = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowClone   = fmt.Errorf("proto: integer overflow")
)

func init() { proto.RegisterFile("util/protoutil/clone.proto", fileDescriptor_clone_96c900215ff8e4e9) }

var fileDescriptor_clone_96c900215ff8e4e9 = []byte{
	// 226 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xe2, 0x92, 0x2a, 0x2d, 0xc9, 0xcc,
	0xd1, 0x2f, 0x28, 0xca, 0x2f, 0xc9, 0x07, 0xb3, 0x92, 0x73, 0xf2, 0xf3, 0x52, 0xf5, 0xc0, 0x7c,
	0x21, 0x89, 0xe4, 0xfc, 0xe4, 0xec, 0xa2, 0xfc, 0xc4, 0xe4, 0x0c, 0x3d, 0x90, 0x9c, 0x1e, 0x5c,
	0x95, 0x94, 0x48, 0x7a, 0x7e, 0x7a, 0x3e, 0x98, 0xab, 0x0f, 0x62, 0x41, 0x64, 0x94, 0x56, 0x33,
	0x72, 0x89, 0x07, 0xa5, 0x26, 0x97, 0x16, 0x15, 0x67, 0x96, 0xa5, 0x3a, 0xe6, 0xa5, 0x84, 0xe6,
	0x81, 0x4d, 0x4b, 0x4c, 0xca, 0x49, 0x15, 0xb2, 0xe7, 0x62, 0x2c, 0x92, 0x60, 0x54, 0x60, 0xd4,
	0xe0, 0x36, 0x32, 0xd4, 0xc3, 0x65, 0xae, 0x1e, 0x0e, 0xdd, 0x41, 0x8c, 0x45, 0x42, 0xfe, 0x5c,
	0x2c, 0xa5, 0xa5, 0x99, 0x29, 0x12, 0x4c, 0x0a, 0x8c, 0x1a, 0x3c, 0x4e, 0xd6, 0x27, 0xee, 0xc9,
	0x33, 0xdc, 0xba, 0x27, 0x6f, 0x9c, 0x9e, 0x59, 0x92, 0x51, 0x9a, 0xa4, 0x97, 0x9c, 0x9f, 0xab,
	0x0f, 0x37, 0x35, 0x25, 0x09, 0xc1, 0xd6, 0x2f, 0xc8, 0x4e, 0xd7, 0x07, 0xfb, 0x0c, 0xa4, 0x5b,
	0x2f, 0x34, 0xd4, 0xd3, 0x25, 0x08, 0x6c, 0x90, 0x93, 0xf6, 0x89, 0x87, 0x72, 0x0c, 0x27, 0x1e,
	0xc9, 0x31, 0x5e, 0x78, 0x24, 0xc7, 0x78, 0xe3, 0x91, 0x1c, 0xe3, 0x83, 0x47, 0x72, 0x8c, 0x13,
	0x1e, 0xcb, 0x31, 0x5c, 0x78, 0x2c, 0xc7, 0x70, 0xe3, 0xb1, 0x1c, 0x43, 0x14, 0x27, 0xdc, 0x61,
	0x49, 0x6c, 0x60, 0xa6, 0x31, 0x20, 0x00, 0x00, 0xff, 0xff, 0x4f, 0x54, 0x1c, 0xcf, 0x2f, 0x01,
	0x00, 0x00,
}
