import 'package:kernel/ast.dart';
import 'package:vm/keep_source/base.dart';

import 'constant.dart';
import 'flutter_sdk.dart';

StringBuffer buildNameParameterStr(Member member) {
  StringBuffer stringBuffer = StringBuffer();
  List<VariableDeclaration> namedParameters = member.function!.namedParameters;
  int count = member.function!.namedParameters.length;
  StringBuffer buffer = new StringBuffer();

  for (int index = 0; index < count; index++) {
    VariableDeclaration declaration = namedParameters[index];
    String value =
        "aot_keep_vm_entry_point_transform(jsonMap['${declaration.name}'])${(dynamicartNullSafety && declaration.type.declaredNullability == Nullability.nonNullable) ? '!' : ''}";
    String name = declaration.name!;
    if (name.startsWith("\$creationLocationd")) {
      continue;
    }
    buffer.write("${name}:${value},");
  }
  String content = buffer.toString();
  if (content.endsWith(",")) {
    content = content.substring(0, content.length - 1);
  }
  stringBuffer.write(content);
  return stringBuffer;
}

StringBuffer buildParameterStr(FunctionNode function) {
  int count = function.positionalParameters.length;
  StringBuffer buffer = new StringBuffer();
  for (int index = 0; index < count; index++) {
    VariableDeclaration vd = function.positionalParameters[index];
    buffer.write(getParameterValue(vd.name, vd.type.declaredNullability));

    if (index != count - 1) {
      buffer.write(",");
    }
  }
  return buffer;
}

String buildGetMethod(Procedure procedure) {
  StringBuffer buffer = new StringBuffer();

  buffer.write("print(\"\${${constructorName}.${procedure.name.text}}\");");
  return buffer.toString();
}

String buildLibraryGetMethod(Procedure procedure, {String? alias}) {
  StringBuffer buffer = new StringBuffer();
  if (!isEmpty(alias)) {
    buffer.write("print(\"\${${alias}.${procedure.name.text}}\");");
  } else {
    buffer.write("print(\"\${${procedure.name.text}}\");");
  }

  return buffer.toString();
}

String buildGetField(Field field) {
  StringBuffer stringBuffer = new StringBuffer();
  if (field.enclosingClass == null) {
    stringBuffer.write("print(\"\${${field.name.text}}\");");
  } else {
    stringBuffer.write("print(\"\${${constructorName}.${field.name.text}}\");");
  }
  return stringBuffer.toString();
}

String buildLibraryGetField(Field field, {String? alias}) {
  StringBuffer stringBuffer = new StringBuffer();
  if (!isEmpty(alias)) {
    stringBuffer.write("print(\"\${${alias}.${field.name.text}}\");");
  } else {
    stringBuffer.write("print(\"\${${field.name.text}}\");");
  }
  return stringBuffer.toString();
}

String buildSetField(Field field) {
  StringBuffer stringBuffer = new StringBuffer();

  stringBuffer.write("${constructorName}" + "." + field.name.text);

  stringBuffer.write(
      "=${getParameterValue(field.name.text, field.type.declaredNullability)};");
  return stringBuffer.toString();
}

String buildLibrarySetField(Field field, {String? alias}) {
  StringBuffer stringBuffer = new StringBuffer();
  if (!isEmpty(alias)) {
    stringBuffer.write("${alias}.${field.name.text}");
  } else {
    stringBuffer.write(field.name.text);
  }

  stringBuffer.write(
      "=${getParameterValue(field.name.text, field.type.declaredNullability)};");
  return stringBuffer.toString();
}

String buildSetMethod(Procedure procedure) {
  StringBuffer buffer = new StringBuffer();
  String value = getParameterValue(
      procedure.name.text, procedure.function.returnType.declaredNullability);

  buffer.write("${constructorName}.${procedure.name.text} = ${value};");

  return buffer.toString();
}

String buildLibrarySetMethod(Procedure procedure, {String? alias}) {
  StringBuffer buffer = new StringBuffer();
  String value = getParameterValue(
      procedure.name.text, procedure.function.returnType.declaredNullability);
  if (!isEmpty(alias)) {
    buffer.write("${alias}.${procedure.name.text} = ${value};");
  } else {
    buffer.write("${procedure.name.text} = ${value};");
  }

  return buffer.toString();
}

StringBuffer buildStaticSetMethod(Procedure procedure) {
  StringBuffer buffer = new StringBuffer();
  Class? clz = procedure.enclosingClass;
  String value = getParameterValue(
      procedure.name.text, procedure.function.returnType.declaredNullability);
  buffer.write("${clz?.name}.${procedure.name.text} = ${value};");

  return buffer;
}

StringBuffer buildStaticGetMethod(Procedure procedure) {
  StringBuffer buffer = new StringBuffer();
  Class? clz = procedure.enclosingClass;
  buffer.write("print(\"\${${clz?.name}.${procedure.name.text}}\");");

  return buffer;
}

StringBuffer buildStaticMethod(SourceProducer producer, Procedure procedure) {
  Class? clz = procedure.enclosingClass;
  StringBuffer buffer = new StringBuffer();
  DartType type = procedure.function.returnType;
  StringBuffer paramBuffer = new StringBuffer();
  paramBuffer.write(buildParameterStr(procedure.function));
  if (procedure.function.requiredParameterCount > 0 &&
      procedure.function.namedParameters.length > 0) {
    paramBuffer.write(",");
  }
  paramBuffer.write(buildNameParameterStr(procedure));
  String typeParamsStr =
      producer.typeParametersToStr(procedure.function.typeParameters);
  if (type is VoidType) {
    buffer.write("${clz?.name}.${procedure.name.text}${typeParamsStr}(");
    buffer.write(paramBuffer);
    buffer.write(");");
  } else {
    buffer.write(
        "print(\"\${${clz?.name}.${procedure.name.text}${typeParamsStr}(");
    buffer.write(paramBuffer);
    buffer.write(")}");
    buffer.write("\");");
  }

  return buffer;
}

String buildStaticConstructMethod(SourceProducer producer, Procedure procedure,
    {String? alias}) {
  StringBuffer content = new StringBuffer();
  Class? clz = procedure.enclosingClass;
  String typeParamsStr =
      producer.typeParametersToStr(procedure.function.typeParameters);
  if (isEmpty(alias)) {
    content.write("${clz?.name}.${procedure.name.text}${typeParamsStr}(");
  } else {
    content
        .write("${alias}.${clz?.name}.${procedure.name.text}${typeParamsStr}(");
  }

  content.write(buildParameterStr(procedure.function));
  if (procedure.function.requiredParameterCount > 0 &&
      procedure.function.namedParameters.length > 0) {
    content.write(",");
  }
  content.write(buildNameParameterStr(procedure));
  content.write(")");

  return content.toString();
}

String buildOperatorMethod(Procedure procedure) {
  StringBuffer buffer = new StringBuffer();
  String value = getParameterValue(
      "child", procedure.function.returnType.declaredNullability);
  if (procedure.name.text == "==") {
    buffer.writeln("print(\"\${_construct==${value}}\");");
  } else if (procedure.name.text == "[]") {
    buffer.writeln("print(\"\${_construct[${value}]}\");");
  } else if (procedure.name.text == "-") {
    buffer.writeln("print(\"\${_construct-${value}}\");");
  } else if (procedure.name.text == "+") {
    buffer.writeln("print(\"\${_construct+${value}}\");");
  } else if (procedure.name.text == "*") {
    buffer.writeln("print(\"\${_construct*${value}}\");");
  } else if (procedure.name.text == "/") {
    buffer.writeln("print(\"\${_construct/${value}}\");");
  } else if (procedure.name.text == "~/") {
    buffer.writeln("print(\"\${_construct~/${value}}\");");
  } else if (procedure.name.text == "[]=") {
    buffer.writeln("print(\"\${_construct[${value}]=${value}}\");");
  } else if (procedure.name.text == "&") {
    buffer.writeln("print(\"\${_construct&${value}}\");");
  } else if (procedure.name.text == "|") {
    buffer.writeln("print(\"\${_construct|${value}}\");");
  } else if (procedure.name.text == "<<") {
    buffer.writeln("print(\"\${_construct<<${value}}\");");
  } else if (procedure.name.text == ">>") {
    buffer.writeln("print(\"\${_construct>>${value}}\");");
  } else if (procedure.name.text == "<") {
    buffer.writeln("print(\"\${_construct<${value}}\");");
  } else if (procedure.name.text == ">") {
    buffer.writeln("print(\"\${_construct>${value}}\");");
  } else if (procedure.name.text == "<=") {
    buffer.writeln("print(\"\${_construct<=${value}}\");");
  } else if (procedure.name.text == ">=") {
    buffer.writeln("print(\"\${_construct>=${value}}\");");
  } else if (procedure.name.text == "unary-") {
    buffer.writeln("print(\"\${-_construct}\");");
  } else if (procedure.name.text == "^") {
    buffer.writeln("print(\"\${_construct^${value}}\");");
  } else if (procedure.name.text == "%") {
    buffer.writeln("print(\"\${_construct%${value}}\");");
  } else if (procedure.name.text == "~") {
    buffer.writeln("print(\"\${~_construct}\");");
  } else if (procedure.name.text == ">>>") {
    buffer.writeln("print(\"\${_construct>>>${value}}\");");
  } else {
    throw "no Operator Process";
  }
  return buffer.toString();
}

String buildMethod(SourceProducer producer, Procedure procedure) {
  StringBuffer buffer = new StringBuffer();

  DartType type = procedure.function.returnType;
  String typeParamsStr =
      producer.typeParametersToStr(procedure.function.typeParameters);

  if (type is VoidType) {
    if (procedure.enclosingClass == null) {
      buffer.write("${procedure.name.text}${typeParamsStr}(");
    } else {
      buffer
          .write("${constructorName}.${procedure.name.text}${typeParamsStr}(");
    }
    buffer.write(buildParameterStr(procedure.function));
    if (procedure.function.requiredParameterCount > 0 &&
        procedure.function.namedParameters.length > 0) {
      buffer.write(",");
    }
    buffer.write(buildNameParameterStr(procedure));

    buffer.write(");");
  } else {
    buffer.write(
        "print(\"\${${constructorName}.${procedure.name.text}${typeParamsStr}");
    buffer.write("(");

    buffer.write(buildParameterStr(procedure.function));
    if (procedure.function.requiredParameterCount > 0 &&
        procedure.function.namedParameters.length > 0) {
      buffer.write(",");
    }
    buffer.write(buildNameParameterStr(procedure));

    buffer.write(")}");
    buffer.write("\");");
  }
  return buffer.toString();
}

String getParameterValue(String? parameterName, Nullability nullability) {
  return "aot_keep_vm_entry_point_transform(jsonMap['${parameterName}'])${(dynamicartNullSafety && nullability == Nullability.nonNullable) ? '!' : ''}";
}

String getPackageName(Library lib) {
  if ("${lib.importUri}" == "dart:_http") {
    return "dart:io";
  }
  return "${lib.importUri}";
}

bool isInKeepFlutterSDK(Library lib) {
  String packageName = getPackageName(lib);
  if (!packageName.startsWith("package:flutter/")) {
    return false;
  }

  if (packageName.startsWith("package:flutter/") &&
      packageName.endsWith("_web.dart")) {
    return false;
  }
  return true;
}

bool isDartSDK(Library lib) {
  String packageName = getPackageName(lib);
  if (packageName.startsWith("dart:")) {
    return true;
  }
  return false;
}

bool isPrivateClass(Class clz) {
  if (clz.name.startsWith("_")) {
    return true;
  }
  return false;
}

bool isPrivateLibrary(Library lib) {
  if (getPackageName(lib).startsWith("dart:_")) {
    return true;
  }
  return false;
}

bool isPrivateProcedure(Procedure procedure) {
  if (procedure.name.text.startsWith("_")) {
    return true;
  }
  return false;
}

bool isPrivateField(Field field) {
  if (field.name.text.startsWith("_")) {
    return true;
  }
  return false;
}

bool isPrivateConstructor(Constructor constructor) {
  if (constructor.name.text.startsWith("_")) {
    return true;
  }
  return false;
}

bool isEmpty(String? str) {
  if (str == null || str.trim().length == 0) {
    return true;
  }
  return false;
}

String getLibraryName(Library lib) {
  String packageName = getPackageName(lib);
  return packageName.startsWith("package:")
      ? packageName.substring("package:".length, packageName.indexOf("/"))
      : packageName.substring("dart:".length);
}
