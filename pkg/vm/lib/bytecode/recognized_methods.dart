// Copyright (c) 2018, the Dart project authors.  Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

library vm.bytecode.recognized_methods;

import 'package:kernel/ast.dart';
import 'package:kernel/type_environment.dart' show StaticTypeContext;

import 'dbc.dart';
import 'generics.dart' show getStaticType;

class RecognizedMethods {
  static const binaryIntOps = <String, Opcode>{
    '+': Opcode.kAddInt,
    '-': Opcode.kSubInt,
    '*': Opcode.kMulInt,
    '~/': Opcode.kTruncDivInt,
    '%': Opcode.kModInt,
    '&': Opcode.kBitAndInt,
    '|': Opcode.kBitOrInt,
    '^': Opcode.kBitXorInt,
    '<<': Opcode.kShlInt,
    '>>': Opcode.kShrInt,
    '==': Opcode.kCompareIntEq,
    '>': Opcode.kCompareIntGt,
    '<': Opcode.kCompareIntLt,
    '>=': Opcode.kCompareIntGe,
    '<=': Opcode.kCompareIntLe,
  };

  static const binaryDoubleOps = <String, Opcode>{
    '+': Opcode.kAddDouble,
    '-': Opcode.kSubDouble,
    '*': Opcode.kMulDouble,
    '/': Opcode.kDivDouble,
    '==': Opcode.kCompareDoubleEq,
    '>': Opcode.kCompareDoubleGt,
    '<': Opcode.kCompareDoubleLt,
    '>=': Opcode.kCompareDoubleGe,
    '<=': Opcode.kCompareDoubleLe,
  };

  final StaticTypeContext staticTypeContext;

  RecognizedMethods(this.staticTypeContext);

  DartType staticType(Expression expr) =>
      getStaticType(expr, staticTypeContext);

  bool isInt(DartType type) =>
      type == staticTypeContext.typeEnvironment.coreTypes.intLegacyRawType ||
      type == staticTypeContext.typeEnvironment.coreTypes.intNullableRawType ||
      type == staticTypeContext.typeEnvironment.coreTypes.intNonNullableRawType;

  bool isDouble(DartType type) =>
      type == staticTypeContext.typeEnvironment.coreTypes.doubleLegacyRawType ||
      type ==
          staticTypeContext
              .typeEnvironment.coreTypes.doubleNonNullableRawType ||
      type == staticTypeContext.typeEnvironment.coreTypes.doubleNullableRawType;

  Opcode? specializedBytecodeForInstance(InstanceInvocation node) {
    final args = node.arguments;
    if (!args.named.isEmpty) {
      return null;
    }

    final Expression receiver = node.receiver;
    final String selector = node.name.text;

    switch (args.positional.length) {
      case 0:
        return specializedBytecodeForUnaryOp(selector, receiver);
      case 1:
        return specializedBytecodeForBinaryOp(
            selector, receiver, args.positional.single);
      default:
        return null;
    }
  }

  Opcode? specializedBytecodeForDynamic(DynamicInvocation node) {
    final args = node.arguments;
    if (!args.named.isEmpty) {
      return null;
    }

    final Expression receiver = node.receiver;
    final String selector = node.name.text;

    switch (args.positional.length) {
      case 0:
        return specializedBytecodeForUnaryOp(selector, receiver);
      case 1:
        return specializedBytecodeForBinaryOp(
            selector, receiver, args.positional.single);
      default:
        return null;
    }
  }

  Opcode? specializedBytecodeForFunction(FunctionInvocation node) {
    final args = node.arguments;
    if (!args.named.isEmpty) {
      return null;
    }

    final Expression receiver = node.receiver;
    final String selector = node.name.text;

    switch (args.positional.length) {
      case 0:
        return specializedBytecodeForUnaryOp(selector, receiver);
      case 1:
        return specializedBytecodeForBinaryOp(
            selector, receiver, args.positional.single);
      default:
        return null;
    }
  }

  Opcode? specializedBytecodeForLocalFunction(LocalFunctionInvocation node) {
    final args = node.arguments;
    if (!args.named.isEmpty) {
      return null;
    }

    final String selector = node.name.text;

    switch (args.positional.length) {
      case 0:
        return specializedBytecodeForUnaryOpLocal(selector, node);
      case 1:
        return specializedBytecodeForBinaryOpLocal(
            selector, node, args.positional.single);
      default:
        return null;
    }
  }

  Opcode? specializedBytecodeForEqauls(EqualsCall node) {
    final String selector = '==';

    return specializedBytecodeForBinaryOp(selector, node.left, node.right);
  }

  Opcode? specializedBytecodeForUnaryOp(String selector, Expression arg) {
    if (selector == 'unary-') {
      final argType = staticType(arg);
      if (isInt(argType)) {
        return Opcode.kNegateInt;
      } else if (isDouble(argType)) {
        return Opcode.kNegateDouble;
      }
    }
    return null;
  }

  Opcode? specializedBytecodeForUnaryOpLocal(
      String selector, LocalFunctionInvocation node) {
    if (selector == 'unary-') {
      final argType = node.functionType.returnType;
      if (isInt(argType)) {
        return Opcode.kNegateInt;
      } else if (isDouble(argType)) {
        return Opcode.kNegateDouble;
      }
    }
    return null;
  }

  Opcode? specializedBytecodeForBinaryOp(
      String selector, Expression a, Expression b) {
    if (selector == '==' && (a is NullLiteral || b is NullLiteral)) {
      return Opcode.kEqualsNull;
    }

    final aType = staticType(a);
    final bType = staticType(b);

    if (isInt(aType) && isInt(bType)) {
      return binaryIntOps[selector];
    }
    if (isDouble(aType) && isDouble(bType)) {
      return binaryDoubleOps[selector];
    }
    return null;
  }

  Opcode? specializedBytecodeForBinaryOpLocal(
      String selector, LocalFunctionInvocation a, Expression b) {
    if (selector == '==' && (a is NullLiteral || b is NullLiteral)) {
      return Opcode.kEqualsNull;
    }

    final aType = a.functionType.returnType;
    final bType = staticType(b);

    if (isInt(aType) && isInt(bType)) {
      return binaryIntOps[selector];
    }
    if (isDouble(aType) && isDouble(bType)) {
      return binaryDoubleOps[selector];
    }
    return null;
  }
}
