import 'package:kernel/ast.dart';
import 'package:vm/keep_source/flutter_sdk.dart';

String vm_entry_point = "@pragma(\"vm:entry-point\")";

Map<Class, List<Class>> map = new Map();
const String constructorName = "_construct";

String importCommonUri = "import 'aot_keep_vm_entry_point.dart';";

String commonContent = """
Map<String, dynamic> jsonMap = Map<String, dynamic>();

enum ResponsePayloadKind {
  /// Response payload is a Dart string.
  String,

  /// Response payload is a binary (Uint8List).
  Binary,

  /// Response payload is a string encoded as UTF8 bytes (Uint8List).
  Utf8String,
}

dynamic aot_keep_vm_entry_point_transform(dynamic jsonObj, {dynamic defaultValue}) {
  if (jsonObj != null) {
    return jsonObj;
  } else if (defaultValue) {
    return defaultValue;
  }

  return null;
}
  """;
String aotKeepVmEntryPointFileName = "aot_keep_vm_entry_point";

List<Uri> get keepPackageNames {
  if (_keepPackageNames == null) {
    _keepPackageNames = <Uri>[];
    for (String item in dartPackageNames) {
      _keepPackageNames!.add(Uri.parse(item));
    }
  }
  print("_keepPackageNames:${_keepPackageNames}\n");
  return _keepPackageNames!;
}

List<Uri>? _keepPackageNames;

List<String> dartPackageNames = [
  "dart:ui",
  "dart:isolate",
  "dart:collection",
  "dart:io",
  "dart:async",
  "dart:developer",
  "dart:convert",
  "dart:typed_data",
  "dart:core",
  "dart:math",
];
