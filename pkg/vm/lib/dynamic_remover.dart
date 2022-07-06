import 'dart:io';

import 'package:kernel/ast.dart' hide MapEntry;
import 'package:front_end/src/api_prototype/compiler_options.dart'
    show CompilerOptions;

import 'keep_source/gen_keep_source.dart';
import 'keep_source/utils.dart';

Map<String, List<String>> hostClasses = new Map();

bool isGenerateBytecode(Library lib, CompilerOptions compileOptions) {
  if (compileOptions.hotUpdate &&
      compileOptions.hotUpdateHostLoadedLibs
          .contains(lib.importUri.toString())) {
    return false;
  }
  _generateMixinClass(compileOptions);

  if (!isDynamicLib(lib, compileOptions)) {
    bool isGenBytecode = false;
    List<String>? clzs = hostClasses[getPackageName(lib)];
    for (Class clz in lib.classes) {
      if (clzs == null || !clzs.contains(clz.name)) {
        isGenBytecode = true;
        break;
      }
    }
    return isGenBytecode;
  }
  return true;
}

void _generateMixinClass(CompilerOptions compileOptions) {
  if (compileOptions.hostDillComponent != null && hostClasses.length == 0) {
    Component hostComponent = compileOptions.hostDillComponent!;
    for (Library lib in hostComponent.libraries) {
      if (isDynamicLib(lib, compileOptions)) {
        continue;
      }
      for (Class clz in lib.classes) {
        String packageName = getPackageName(clz.enclosingLibrary);
        if (!hostClasses.containsKey(packageName)) {
          hostClasses[packageName] = [];
        }
        hostClasses[packageName]!.add(clz.name);
      }
    }
  }
}
