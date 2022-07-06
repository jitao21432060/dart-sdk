import 'dart:collection';
import 'dart:convert';
import 'dart:io';
import 'dart:async';

import 'package:front_end/src/api_unstable/vm.dart' show CompilerOptions;
import 'package:kernel/ast.dart';
import 'constant.dart';
import 'dart_sdk.dart';
import 'utils.dart';

const String _preMethodName = "_aot_keep_vm_entry_point";
int _suffixFileName = 0;
bool dynamicartNullSafety = false;

String _getFileName() {
  return "aot_keep_vm_entry_point${_suffixFileName++}.dart";
}

class ImportDetail {
  Set<String> shows = new Set();
  Set<String> hides = new Set();
}

abstract class SourceProducer {
  final Uri source;
  final CompilerOptions options;
  final Component component;
  final Map<Class, Class> classMap;
  late List<String> fileNames;
  late List<File> files;

  Set<Class> allClass = new Set();

  StringBuffer buffer = new StringBuffer();

  List<String> subClassSources = <String>[];

  List<String> keepClassInvokeMethodSources = <String>[];

  Map<Class, String> keepClassMethod = new Map();

  Map<Class, String> keepClassMethodName = new Map();

  Map<String, ImportDetail> importUris = new HashMap();

  late _SubclassGenerator subclassGenerator;

  int methodIndex = 1;

  int classIndex = 1;

  String _preClassName = "_A";

  Set<String> alreadyKeepClassNames = Set();

  late Library currentLib;

  SourceProducer(this.source, this.options, this.component, this.classMap) {
    fileNames = [];
    files = [];
  }

  File getFile() {
    String fileName = _getFileName();
    fileNames.add(fileName);
    String packagesFileUri = options.packagesFileUri!.toFilePath();
    int index = packagesFileUri.lastIndexOf("/");
    String directory = packagesFileUri.substring(0, index);
    File f = new File(directory + "/../lib/" + fileName);
    files.add(f);
    return f;
  }

  List<File> getFiles() {
    return files;
  }

  List<String> getFileNames() {
    return fileNames;
  }

  bool canProcessLibrary(Library lib);

  void _removeNeedKeepClass(Class clz, List<Class> allClass) {
    if (clz.superclass != null) {
      allClass.remove(clz.superclass);
      _removeNeedKeepClass(clz.superclass!, allClass);
    }
  }

  bool isGenerateSubClassSource(Class clz) {
    return true;
  }

  void generateSubClass() {
    List<Class> clzs = <Class>[];
    HashMap<Class, HashSet<Class>> childrenMap =
        HashMap<Class, HashSet<Class>>();
    for (Class clz in allClass) {
      if (clz.isAbstract && !clz.isMixinDeclaration && canProcessClass(clz)) {
        clzs.add(clz);
      }
    }

    for (Class clz in allClass) {
      if (!clz.isAbstract && canProcessClass(clz)) {
        Class? superClass = clz.superclass;
        while (superClass != null) {
          if (clzs.contains(superClass)) {
            HashSet<Class>? children = childrenMap[superClass];
            if (children == null) {
              children = HashSet();
              childrenMap[superClass] = children;
            }
            children.add(clz);
          }
          superClass = superClass.superclass;
        }
      }
    }

    subclassGenerator = new _SubclassGenerator(
        this, component, keepClassMethod, keepClassMethodName, methodIndex);

    for (Class clz in clzs) {
      if (isGenerateSubClassSource(clz)) {
        subclassGenerator.generateSubClassSource(
            clz, "${_preClassName}${classIndex++}");

        subClassSources.add(subclassGenerator.classSource);
        if (subclassGenerator.invokeMethodStr != null) {
          keepClassInvokeMethodSources.add(subclassGenerator.invokeMethodStr!);
        }
        if (childrenMap[clz] == null || childrenMap[clz]!.length == 1) {
          subclassGenerator.generateSubClassSource(
              clz, "${_preClassName}${classIndex++}");
          subClassSources.add(subclassGenerator.classSource);
        }
      }
    }
    subclassGenerator.dependencyLibs.forEach((lib) {
      addImportLibrary(lib, checkRepeatClass: true);
    });
    subclassGenerator.dependencyLibDependencys.forEach((libd) {
      addImportLibraryDependency(libd);
    });

    for (String item in keepClassInvokeMethodSources) {
      this.buffer.write(item);
    }
  }

  void writeFile() {
    generateSubClass();

    File file = getFile();
    StringBuffer buffer = new StringBuffer();
    String importUri = getImportUri();
    if (importUri != null) {
      buffer.write(importUri);
    }
    buffer.writeln("${importCommonUri}");
    if (importUris.containsKey("package:flutter/src/widgets/constants.dart") &&
        importUris.containsKey("package:flutter/src/material/constants.dart")) {
      importUris.remove("package:flutter/src/widgets/constants.dart");
    }
    importUris.forEach((url, detail) {
      String item = "import '${url}'";
      if (detail.shows.isNotEmpty) {
        item += " show ${detail.shows.join(",")}";
      }
      if (detail.hides.isNotEmpty) {
        item += " hide ${detail.hides.join(",")}";
      }
      item += ";";
      buffer.writeln(item);
    });

    String content = getContent();
    buffer.write(content);

    for (String item in subClassSources) {
      buffer.writeln(item);
    }

    for (Class clz in keepClassMethod.keys) {
      buffer.write(keepClassMethod[clz]);
    }

    if (content != null) {
      file.writeAsStringSync(buffer.toString());
    }
  }

  String getContent() {
    StringBuffer content = new StringBuffer();
    content.writeln("@pragma(\"vm:entry-point\")");
    content.writeln("void aot_keep_vm_entry_point(){");
    if (buffer != null) {
      content.write(buffer);
    }
    content.write("}");
    return content.toString();
  }

  String getImportUri();

  String _buildLibraryMethod(Procedure procedure) {
    DartType type = procedure.function.returnType;
    StringBuffer stringBuffer = new StringBuffer();
    String types = typeParametersToStr(procedure.function.typeParameters);
    if (types != null) {
      stringBuffer.write(types);
    }

    stringBuffer.write("(");
    int count = procedure.function.requiredParameterCount;
    if (types == null) {
      for (int index = 0; index < count; index++) {
        stringBuffer.write("null");
        if (index != count - 1) {
          stringBuffer.write(",");
        }
      }
    } else {
      stringBuffer.write(buildParameterStr(procedure.function));
    }
    if (count > 0 && procedure.function.namedParameters.length > 0) {
      stringBuffer.write(",");
    }

    stringBuffer.write(buildNameParameterStr(procedure));
    StringBuffer buffer = new StringBuffer();
    if (type is VoidType) {
      buffer.write("${procedure.name.text}${stringBuffer});");
    } else {
      buffer.write("print(\"\${${procedure.name.text}${stringBuffer})}\");");
    }
    return buffer.toString();
  }

  String processOperatorMethod(Procedure procedure) {
    return buildOperatorMethod(procedure);
  }

  bool canProcessProcedure(Procedure procedure) {
    if (isPrivateProcedure(procedure)) {
      return false;
    }
    if (procedure.isExtensionMember) {
      return false;
    }
    if (procedure.name.text == 'isInsecureConnectionAllowed') {
      return false;
    }
    return true;
  }

  bool canProcessField(Field field) {
    if (isPrivateField(field)) {
      return false;
    }
    return true;
  }

  bool canProcessConstructor(Constructor construct) {
    if (isPrivateConstructor(construct) ||
        construct.enclosingClass.isAbstract) {
      return false;
    }
    return true;
  }

  bool canProcessClass(Class clz) {
    if (isPrivateClass(clz)) {
      return false;
    }
    return true;
  }

  String? processLibraryProcedure(Procedure procedure) {
    if (!canProcessProcedure(procedure)) {
      return null;
    }
    if (procedure.isGetter) {
      return buildLibraryGetMethod(procedure);
    } else if (procedure.isSetter) {
      return buildLibrarySetMethod(procedure);
    } else {
      return _buildLibraryMethod(procedure);
    }
  }

  void processLibrary(Library library) {
    if (!canProcessLibrary(library)) {
      return;
    }
    if (!canImportLibrary(library)) {
      return;
    }
    currentLib = library;
    buffer.clear();
    importUris.clear();
    keepClassMethod.clear();
    keepClassMethodName.clear();
    keepClassInvokeMethodSources.clear();
    subClassSources.clear();
    allClass.clear();
    alreadyKeepClassNames.clear();

    String packageName = getPackageName(library);
    for (Procedure procedure in library.procedures) {
      String? content = processLibraryProcedure(procedure);
      if (content != null) {
        buffer.writeln(content);
      }
    }
    for (Field field in library.fields) {
      if (!canProcessField(field)) {
        continue;
      }

      String content = buildLibraryGetField(field);
      buffer.writeln(content);
      if (!field.isFinal && !field.isConst) {
        String content = buildLibrarySetField(field);
        buffer.writeln(content);
      }
    }

    allClass.addAll(library.classes);

    for (Class clz in library.classes) {
      if (!canProcessClass(clz)) {
        continue;
      }

      alreadyKeepClassNames.add(clz.name);

      String? content;
      if (clz.isEnum) {
        content = processEnum(clz);
      } else {
        content = processClass(clz);
      }
      if (content != null) {
        buffer.write(content);
      }
    }

    addImportLibrary(library);

    library.dependencies.forEach((libd) {
      addImportLibraryDependency(libd);
    });

    writeFile();
  }

  void addImportLibraryDependency(LibraryDependency dependency) {
    if (!dependency.isImport) {
      return;
    }
    if (this is DartLibraryProducer) {
      addImportLibrary(dependency.targetLibrary, checkRepeatClass: true);
    } else {
      Library library = dependency.targetLibrary;
      Set<String> shows = Set();
      Set<String> hides = Set();
      dependency.combinators.forEach((combinator) {
        if (combinator.isShow) {
          shows.addAll(combinator.names);
        } else if (combinator.isHide) {
          hides.addAll(combinator.names);
        }
      });
      addImportLibrary(library,
          shows: shows, hides: hides, checkRepeatClass: true);
    }
  }

  bool canImportLibrary(Library library) {
    String packageName = getPackageName(library);
    if (packageName.startsWith("dart:_")) {
      return false;
    }
    var split = packageName.split("/");
    bool excludeImport = split.isNotEmpty &&
        split.last.startsWith("_") &&
        (split.last.endsWith("_io.dart") || split.last.endsWith("_web.dart"));
    if (excludeImport) {
      return false;
    }
    return true;
  }

  void addImportLibrary(Library library,
      {Set<String>? shows, Set<String>? hides, bool checkRepeatClass = false}) {
    if (!canImportLibrary(library)) {
      return;
    }
    String packageName = getPackageName(library);
    String curPackageName = getPackageName(currentLib);
    if (checkRepeatClass && curPackageName != packageName) {
      for (Class clz in library.classes) {
        if (alreadyKeepClassNames.contains(clz.name)) {
          if (hides == null) {
            hides = Set();
          }
          hides.add(clz.name);
        }
      }
    }
    ImportDetail importDetail = importUris.putIfAbsent(packageName, () {
      ImportDetail importDetail = ImportDetail();
      if (shows != null) {
        importDetail.shows.addAll(shows);
      }
      if (hides != null) {
        importDetail.hides.addAll(hides);
      }
      return importDetail;
    });
    if (shows != null) {
      importDetail.shows.addAll(shows);
    }
    if (hides != null) {
      importDetail.hides.addAll(hides);
    }
  }

  String processEnum(Class clz) {
    String? methodName;
    if (!keepClassMethod.containsKey(clz)) {
      StringBuffer buffer = new StringBuffer();
      methodIndex++;
      methodName = "${_preMethodName}$methodIndex";
      keepClassMethodName[clz] = methodName;
      buffer.write("void ${methodName}(${clz.name} ${constructorName})");
      buffer.writeln("{");
      buffer.writeln("${constructorName}.toString();");
      buffer.writeln("${constructorName}.index.toString();");
      buffer.writeln("}");
      keepClassMethod[clz] = buffer.toString();
    } else {
      methodName = keepClassMethodName[clz];
    }

    StringBuffer buffer = new StringBuffer();
    for (Field field in clz.fields) {
      if (!field.name.text.startsWith("_") &&
          field.name.text != "index" &&
          field.name.text != "values") {
        buffer.writeln("${methodName}(${clz.name}.${field.name.text});");
      }
    }
    buffer.writeln("${clz.name}.values.toString();");
    return buffer.toString();
  }

  String? processClass(Class clz) {
    List<String> constructors = <String>[];
    List<String> statics = <String>[];
    // non static function(procedure) and field
    List<String> noStaticList = <String>[];
    Set<String> alreadyInvokeProduces = new Set();
    Set<String> alreadyInvokeGetProduces = new Set();
    Set<String> alreadyInvokeSetProduces = new Set();

    for (Constructor construct in clz.constructors) {
      if (!canProcessConstructor(construct)) {
        continue;
      }
      String content = _processConstructor(construct);
      if (content != null && content.isNotEmpty) {
        constructors.add(content);
      }
    }
    for (Procedure procedure in clz.procedures) {
      if (!canProcessProcedure(procedure)) {
        continue;
      }
      if (procedure.isFactory) {
        String factory = processFactoryProcedure(procedure);
        if (factory != null && factory.isNotEmpty) {
          constructors.add(factory);
        }
      } else if (procedure.isStatic) {
        if (procedure.isGetter) {
          DartType type = procedure.function.returnType;
          if (type is InterfaceType) {
            Class returnClass = type.classNode;
            if (getPackageName(returnClass.enclosingLibrary) ==
                    getPackageName(clz.enclosingLibrary) &&
                returnClass.name == clz.name) {
              constructors.add("${clz.name}.${procedure.name.text}");
            } else {
              statics.add(processStaticGetMethod(procedure));
            }
          } else {
            statics.add(processStaticGetMethod(procedure));
          }
        } else if (procedure.isSetter) {
          statics.add(processStaticSetMethod(procedure));
        } else {
          Class clz = procedure.enclosingClass!;
          DartType type = procedure.function.returnType;
          if (type is InterfaceType) {
            Class returnClass = type.classNode;
            if (getPackageName(returnClass.enclosingLibrary) ==
                    getPackageName(clz.enclosingLibrary) &&
                returnClass.name == clz.name) {
              String factory = buildStaticConstructMethod(this, procedure);
              if (factory != null && factory.isNotEmpty) {
                constructors.add(factory);
              }
            } else {
              statics.add(processStaticMethod(procedure));
            }
          } else {
            statics.add(processStaticMethod(procedure));
          }
        }
      }
    }

    for (Field field in clz.fields) {
      if (!canProcessField(field) || !field.isStatic) {
        continue;
      }
      DartType type = field.type;
      if (type is InterfaceType) {
        Class returnClass = type.classNode;
        if (getPackageName(returnClass.enclosingLibrary) ==
                getPackageName(clz.enclosingLibrary) &&
            returnClass.name == clz.name) {
          constructors.add(field.enclosingClass!.name + "." + field.name.text);
        } else {
          statics.add(processStaticGetField(field));
        }
      } else {
        statics.add(processStaticGetField(field));
      }
      if (!field.isFinal && !field.isConst) {
        statics.add(processStaticSetField(field));
      }
    }
    if (constructors.isEmpty && !clz.isAbstract) {
      constructors.add(getParameterValue(clz.name, Nullability.nonNullable));
    }

    if (constructors.isEmpty) {
      if (statics.isNotEmpty) {
        StringBuffer buffer = new StringBuffer();
        for (String item in statics) {
          buffer.writeln(item);
        }
        return buffer.toString();
      }
      return null;
    }

    for (Procedure procedure in clz.procedures) {
      if (!canProcessProcedure(procedure) ||
          procedure.isFactory ||
          procedure.isStatic) {
        continue;
      }

      if (procedure.isGetter) {
        alreadyInvokeGetProduces.add(procedure.name.text);
        noStaticList.add(buildGetMethod(procedure));
      } else if (procedure.isSetter) {
        alreadyInvokeSetProduces.add(procedure.name.text);
        noStaticList.add(buildSetMethod(procedure));
      } else if (procedure.kind == ProcedureKind.Operator) {
        alreadyInvokeProduces.add(procedure.name.text);
        noStaticList.add(processOperatorMethod(procedure));
      } else {
        alreadyInvokeProduces.add(procedure.name.text);
        noStaticList.add(buildMethod(this, procedure));
      }
    }

    for (Field field in clz.fields) {
      if (canProcessField(field)) {
        if (!field.isStatic) {
          if (!alreadyInvokeGetProduces.contains(field.name.text)) {
            noStaticList.add(buildGetField(field));
            alreadyInvokeGetProduces.add(field.name.text);
          }

          if (!field.isFinal && !field.isConst) {
            if (!alreadyInvokeSetProduces.contains(field.name.text)) {
              noStaticList.add(buildSetField(field));
              alreadyInvokeSetProduces.add(field.name.text);
            }
          }
        }
      }
    }

    StringBuffer buffer = new StringBuffer();
    for (String item in statics) {
      buffer.writeln(item);
    }
    String? methodName;
    if (keepClassMethod.containsKey(clz)) {
      methodName = keepClassMethodName[clz];
    } else {
      methodIndex++;
      methodName = "${_preMethodName}$methodIndex";
      keepClassMethodName[clz] = methodName;
      StringBuffer buffer = new StringBuffer();

      if (dynamicartNullSafety) {
        buffer.writeln("void ${methodName}(${clz.name}? ${constructorName}){");
        buffer.writeln("print(${constructorName}!);");
      } else {
        buffer.writeln("void ${methodName}(${clz.name} ${constructorName}){");
      }
      if (noStaticList.isEmpty) {
        buffer.writeln("print(${constructorName}.toString());");
      } else {
        for (String item in noStaticList) {
          buffer.writeln(item);
        }
      }
      List<String> content = <String>[];

      _keepSuperClass(clz, content,
          excludeGetMethod: alreadyInvokeGetProduces,
          excludeSetMethod: alreadyInvokeSetProduces,
          excludeMethod: alreadyInvokeProduces);
      for (String item in content) {
        buffer.writeln(item);
      }

      buffer.writeln("}");
      keepClassMethod[clz] = buffer.toString();
    }

    for (String item in constructors) {
      buffer.writeln("${methodName}($item);");
    }
    return buffer.toString();
  }

  String _processConstructor(Constructor constructor) {
    StringBuffer content = new StringBuffer();
    Class clz = constructor.enclosingClass;
    String type = typeParametersToStr(clz.typeParameters);
    if (type == null) {
      type = "";
    }
    if (constructor.name.text.trim().isEmpty) {
      content.write("new ${clz.name}");
      content.write(type);
      content.write("(");
    } else {
      content.write("${clz.name}${type}.${constructor.name.text}(");
    }
    content.write(buildParameterStr(constructor.function));
    if (constructor.function.namedParameters.length > 0 &&
        constructor.function.requiredParameterCount > 0) {
      content.write(",");
    }
    content.write(buildNameParameterStr(constructor));
    content.write(")");

    return content.toString();
  }

  String processFactoryProcedure(Procedure factory) {
    if (factory.name.text.trim().isEmpty &&
        factory.enclosingClass!.name == 'List') {
      return '';
    }
    StringBuffer content = new StringBuffer();
    Class? clz = factory.enclosingClass;
    String type = typeParametersToStr(clz?.typeParameters);
    if (type == null) {
      type = "";
    }
    content.write("${clz?.name}");
    if (factory.name.text.isEmpty) {
      content.write("${type}(");
    } else {
      content.write("${type}.${factory.name.text}(");
    }
    content.write(buildParameterStr(factory.function));

    if (factory.function.requiredParameterCount > 0 &&
        factory.function.namedParameters.length > 0) {
      content.write(",");
    }
    content.write(buildNameParameterStr(factory));

    content.write(")");
    return content.toString();
  }

  String processStaticGetMethod(Procedure method) {
    return buildStaticGetMethod(method).toString();
  }

  String processStaticSetMethod(Procedure method) {
    return buildStaticSetMethod(method).toString();
  }

  String processStaticMethod(Procedure method) {
    return buildStaticMethod(this, method).toString();
  }

  String processStaticConstructorMethod(Procedure method) {
    StringBuffer content = new StringBuffer();
    Class? clz = method.enclosingClass;
    content.write("${clz?.name}.${method.name.text}(");
    content.write(buildParameterStr(method.function));
    if (method.function.namedParameters.length > 0 &&
        method.function.requiredParameterCount > 0) {
      content.write(",");
    }
    content.write(buildNameParameterStr(method));

    content.write(")");

    return content.toString();
  }

  String processStaticGetField(Field field) {
    StringBuffer stringBuffer = new StringBuffer();
    stringBuffer.write("print(\"\$");
    stringBuffer.write("{");
    stringBuffer.write(field.enclosingClass!.name + "." + field.name.text);
    stringBuffer.write("}\");");
    return stringBuffer.toString();
  }

  String processStaticSetField(Field field) {
    StringBuffer stringBuffer = new StringBuffer();
    stringBuffer.write(field.enclosingClass!.name + "." + field.name.text);
    String value =
        getParameterValue(field.name.text, field.type.declaredNullability);
    stringBuffer.write("=${value};");
    return stringBuffer.toString();
  }

  void _keepSuperClass(Class clz, List<String> content,
      {Set<String>? excludeGetMethod,
      Set<String>? excludeSetMethod,
      Set<String>? excludeMethod}) {
    if (clz.superclass != null && clz.superclass!.isAnonymousMixin) {
      _buildSuperClass(clz.superclass!, content,
          excludeGetMethod: excludeGetMethod,
          excludeSetMethod: excludeSetMethod,
          excludeMethod: excludeMethod);
      _keepSuperClass(clz.superclass!, content,
          excludeGetMethod: excludeGetMethod,
          excludeSetMethod: excludeSetMethod,
          excludeMethod: excludeMethod);
    }
    // if (clz.mixedInClass != null) {
    //   _buildSuperClass(clz.mixedInClass, content,
    //       excludeGetMethod: excludeGetMethod,
    //       excludeSetMethod: excludeSetMethod,
    //       excludeMethod: excludeMethod);
    //   _keepSuperClass(clz.mixedInClass, content,
    //       excludeGetMethod: excludeGetMethod,
    //       excludeSetMethod: excludeSetMethod,
    //       excludeMethod: excludeMethod);
    // }
    // for (Supertype supertype in clz.implementedTypes) {
    //   _buildSuperClass(supertype.classNode, content,
    //       excludeGetMethod: excludeGetMethod,
    //       excludeSetMethod: excludeSetMethod,
    //       excludeMethod: excludeMethod);
    //   _keepSuperClass(supertype.classNode, content,
    //       excludeGetMethod: excludeGetMethod,
    //       excludeSetMethod: excludeSetMethod,
    //       excludeMethod: excludeMethod);
    // }
  }

  void _buildSuperClass(Class clz, List<String> content,
      {Set<String>? excludeGetMethod,
      Set<String>? excludeSetMethod,
      Set<String>? excludeMethod}) {
    if (_isObject(clz)) {
      return;
    }
    if (clz.name.startsWith("_") || isPrivateLibrary(clz.enclosingLibrary)) {
      for (Procedure procedure in clz.procedures) {
        if (!canProcessProcedure(procedure) ||
            procedure.isFactory ||
            procedure.isStatic) {
          continue;
        }
        if (procedure.isGetter) {
          if (excludeGetMethod == null) {
            content.add(buildGetMethod(procedure));
          } else if (!excludeGetMethod.contains(procedure.name.text)) {
            content.add(buildGetMethod(procedure));
            excludeGetMethod.add(procedure.name.text);
          }
        } else if (procedure.isSetter) {
          if (excludeSetMethod == null) {
            content.add(buildSetMethod(procedure));
          } else if (!excludeSetMethod.contains(procedure.name.text)) {
            content.add(buildSetMethod(procedure));
            excludeSetMethod.add(procedure.name.text);
          }
        } else {
          if (excludeMethod != null &&
              excludeMethod.contains(procedure.name.text)) {
            continue;
          }
          if (excludeMethod != null) {
            excludeMethod.add(procedure.name.text);
          }

          if (procedure.kind == ProcedureKind.Operator) {
            content.add(processOperatorMethod(procedure));
          } else {
            content.add(buildMethod(this, procedure));
          }
        }
      }

      for (Field field in clz.fields) {
        if (canProcessField(field) && !field.isStatic) {
          content.add(buildGetField(field));
          if (!field.isFinal && field.isConst) {
            content.add(buildSetField(field));
          }
        }
      }
    } else {
      if (keepClassMethod.containsKey(clz)) {
        content.add("${keepClassMethodName[clz]}(${constructorName});");
        return;
      }
      methodIndex++;

      addImportLibrary(clz.enclosingLibrary, checkRepeatClass: true);

      StringBuffer buffer = new StringBuffer();
      String methodName = "${_preMethodName}$methodIndex";
      buffer.writeln("void $methodName(${clz.name} ${constructorName}){");

      bool isHasMethod = false;
      for (Procedure procedure in clz.procedures) {
        if (!canProcessProcedure(procedure) ||
            procedure.isFactory ||
            procedure.isStatic) {
          continue;
        }

        if (procedure.isGetter) {
          buffer.writeln(buildGetMethod(procedure));
        } else if (procedure.isSetter) {
          buffer.writeln(buildSetMethod(procedure));
        } else if (procedure.kind == ProcedureKind.Operator) {
          buffer.writeln(processOperatorMethod(procedure));
        } else {
          buffer.writeln(buildMethod(this, procedure));
        }
        isHasMethod = true;
      }

      for (Field field in clz.fields) {
        if (canProcessField(field) && !field.isStatic) {
          buffer.writeln(buildGetField(field));
          if (!field.isFinal && field.isConst) {
            buffer.writeln(buildSetField(field));
          }
        }
      }

      buffer.writeln("}");
      if (isHasMethod) {
        keepClassMethodName[clz] = methodName;
        keepClassMethod[clz] = buffer.toString();
        content.add("${keepClassMethodName[clz]}(${constructorName});");
      }
    }
  }

  String typeParametersToStr(List<TypeParameter>? typeParameters) {
    if (typeParameters == null || typeParameters.isEmpty) {
      return "";
    }

    StringBuffer content = new StringBuffer();
    content.write("<");

    for (int index = 0; index < typeParameters.length; index++) {
      TypeParameter item = typeParameters[index];
      if (item.defaultType is DynamicType) {
        content.write("dynamic");
      } else if (item.defaultType is InterfaceType) {
        InterfaceType type = item.defaultType as InterfaceType;
        if (!type.classNode.isAbstract) {
          content.write("${type.classNode.name}");
        } else if (classMap.containsKey(type.classNode)) {
          content.write("${classMap[type.classNode]?.name}");
          addImportLibrary(classMap[type.classNode]!.enclosingLibrary,
              checkRepeatClass: true);
        } else {
          return "";
        }
      } else {
        return "";
      }
      if (index != typeParameters.length - 1) {
        content.write(",");
      }
    }
    content.write(">");
    return content.toString();
  }
}

class _SubclassGenerator {
  Component component;

  Map<Class, String> keepClassSource = new Map();

  Map<Class, String> keepClassInvokeMethodName = new Map();

  String? invokeMethodStr;

  late String classSource;

  late int methodIndex;

  Set<String> _alreadyGenSourceProduces = new Set();

  Set<String> _alreadyGenSourceGetProduces = new Set();

  Set<String> _alreadyGenSourceFields = new Set();

  Set<String> _alreadyGenSourceSetProduces = new Set();

  Set<String> _alreadyGenSourceClzs = new Set();

  Set<Library> dependencyLibs = Set();
  Set<LibraryDependency> dependencyLibDependencys = Set();

  late String libName;

  SourceProducer producer;

  _SubclassGenerator(this.producer, this.component, this.keepClassSource,
      this.keepClassInvokeMethodName, this.methodIndex);

  void generateSubClassSource(Class clz, String className) {
    libName = getLibraryName(clz.enclosingLibrary);
    classSource = _generate(clz, className);
  }

  String _generate(Class clz, String className) {
    bool isImplements = false;
    int procedureCount = 0;
    for (Procedure procedure in clz.procedures) {
      if (procedure.isFactory) {
        isImplements = true;
        break;
      } else {
        procedureCount++;
      }
    }

    for (Constructor constructor in clz.constructors) {
      if (constructor.name.text.isEmpty || constructor.name.text == clz.name) {
        isImplements = false;
        break;
      } else {
        isImplements = true;
      }
    }

    if (isImplements && procedureCount == 0) {
      return "";
    }

    StringBuffer buffer = new StringBuffer();

    String classSource = utf8
        .decode(component.uriToSource[clz.fileUri]!.source)
        .substring(clz.fileOffset, clz.fileEndOffset);

    buffer.writeln(vm_entry_point);

    if (clz.typeParameters.length > 0) {
      String typeParametersStr = _getClassTypeParametersStr(classSource);
      if (isImplements) {
        buffer.writeln(
            "class ${className}${typeParametersStr.trim()} implements ${clz.name}<");
      } else {
        buffer.writeln(
            "class ${className}${typeParametersStr.trim()} extends ${clz.name}<");
      }
      for (int i = 0; i < clz.typeParameters.length; i++) {
        if (i < clz.typeParameters.length - 1) {
          buffer.write("${clz.typeParameters[i].name},");
        } else {
          buffer.write("${clz.typeParameters[i].name}");
        }
      }
      buffer.write(">{");
    } else {
      if (isImplements) {
        buffer.writeln("class ${className} implements ${clz.name}{");
      } else {
        buffer.writeln("class ${className} extends ${clz.name}{");
      }
    }
    _getDependenciesLibrary(clz);

    String? constructSource = _generateConstructSource(clz, className);
    if (constructSource != null) {
      buffer.write(constructSource);
    }
    _alreadyGenSourceClzs.clear();
    String tmpContent = "";
    List<String> typeList = <String>[];
    for (TypeParameter item in clz.typeParameters) {
      typeList.add(item.name!);
    }
    runZoned(() {
      tmpContent = _generateProcedureAndFieldSource(clz, isImplements);
    }, zoneValues: {
      #typeArgs: null,
      #typeList: [typeList]
    });

    buffer.write(tmpContent);
    _generateSuperClassSource(clz, buffer, isImplements);

    _alreadyGenSourceProduces.clear();
    _alreadyGenSourceGetProduces.clear();
    _alreadyGenSourceSetProduces.clear();
    _alreadyGenSourceFields.clear();
    buffer.write("}");
    return buffer.toString();
  }

  String? _generateConstructSource(Class clz, String className) {
    Constructor? constructor;
    for (Constructor item in clz.constructors) {
      if (item.name.text.isEmpty || item.name.text == clz.name) {
        constructor = item;
      }
    }
    if (constructor == null) {
      return null;
    }
    StringBuffer buffer = new StringBuffer();

    List<String> typeParameterNames = <String>[];
    for (TypeParameter item in constructor.enclosingClass.typeParameters) {
      typeParameterNames.add(item.name!);
    }

    StringBuffer constructorBuffer = new StringBuffer();
    constructorBuffer.write(vm_entry_point);
    constructorBuffer.write("${className}(");

    String content = "";
    List<String> typeList = <String>[];
    for (TypeParameter item in clz.typeParameters) {
      typeList.add(item.name!);
    }
    runZoned(() {
      content = _getFunctionParameters(constructor!.function);
    }, zoneValues: {
      #typeArgs: null,
      #typeList: [typeList]
    });

    constructorBuffer.write(content);
    constructorBuffer.write(")");

    constructorBuffer.write(":super(");
    StringBuffer tmpBuffer = StringBuffer();
    for (int i = 0; i < constructor.function.requiredParameterCount; i++) {
      VariableDeclaration variableDeclaration =
          constructor.function.positionalParameters[i];
      if (!variableDeclaration.name!.startsWith("\$creationLocationd")) {
        if (dynamicartNullSafety &&
            variableDeclaration.type.declaredNullability ==
                Nullability.nonNullable) {
          tmpBuffer.write("${variableDeclaration.name}!");
        } else {
          tmpBuffer.write("${variableDeclaration.name}");
        }
      }
      if (i != constructor.function.requiredParameterCount - 1) {
        tmpBuffer.write(",");
      }
    }
    for (int i = 0; i < constructor.function.namedParameters.length; i++) {
      VariableDeclaration variableDeclaration =
          constructor.function.namedParameters[i];
      if (constructor.function.requiredParameterCount > 0) {
        tmpBuffer.write(",");
      } else if (i != 0) {
        tmpBuffer.write(",");
      }
      if (!variableDeclaration.name!.startsWith("\$creationLocationd")) {
        if (dynamicartNullSafety) {
          tmpBuffer.write(
              variableDeclaration.name! + ":" + "${variableDeclaration.name}!");
        } else {
          tmpBuffer.write(
              variableDeclaration.name! + ":" + "${variableDeclaration.name}");
        }
      }
    }
    for (int i = constructor.function.requiredParameterCount;
        i < constructor.function.positionalParameters.length;
        i++) {
      VariableDeclaration variableDeclaration =
          constructor.function.positionalParameters[i];
      if (constructor.function.requiredParameterCount > 0 ||
          constructor.function.namedParameters.length > 0) {
        tmpBuffer.write(",");
      }
      if (!variableDeclaration.name!.startsWith("\$creationLocationd")) {
        if (dynamicartNullSafety) {
          tmpBuffer.write("${variableDeclaration.name}!");
        } else {
          tmpBuffer.write("${variableDeclaration.name}");
        }
      }
    }
    constructorBuffer.write(tmpBuffer.toString());
    constructorBuffer.write(");");
    buffer.writeln(constructorBuffer);
    return buffer.toString();
  }

  bool _isObjectMethod(Class clz, Procedure procedure) {
    if (clz.superclass!.name != "Object") {
      return false;
    } else {
      if (procedure.enclosingClass!.name == "Object") {
        return true;
      } else {
        return false;
      }
    }
  }

  String _generateProcedureAndFieldSource(Class clz, bool isImplements) {
    if (_alreadyGenSourceClzs.contains(clz.name) ||
        _isObject(clz) ||
        clz.name.contains("&")) {
      return "";
    }
    _alreadyGenSourceClzs.add(clz.name);

    StringBuffer buffer = new StringBuffer();
    List<String> methods = <String>[];

    for (Procedure procedure in clz.procedures) {
      if (_isObjectMethod(clz, procedure)) {
        continue;
      }

      if (isPrivateProcedure(procedure) ||
          procedure.isStatic ||
          procedure.isFactory) {
        continue;
      }

      if (procedure.isGetter) {
        methods.add(buildGetMethod(procedure));
      } else if (procedure.isSetter) {
        methods.add(buildSetMethod(procedure));
      } else if (procedure.kind == ProcedureKind.Operator) {
        methods.add(buildOperatorMethod(procedure));
      } else {
        methods.add(buildMethod(producer, procedure));
      }

      String methodName = procedure.name.text;

      if (procedure.isGetter) {
        if (_alreadyGenSourceGetProduces.contains(methodName) ||
            _alreadyGenSourceFields.contains(methodName)) {
          continue;
        }
        _alreadyGenSourceGetProduces.add(methodName);
      } else if (procedure.isSetter) {
        if (_alreadyGenSourceSetProduces.contains(methodName) ||
            _alreadyGenSourceFields.contains(methodName)) {
          continue;
        }
        _alreadyGenSourceSetProduces.add(methodName);
      } else {
        if (_alreadyGenSourceProduces.contains(methodName)) {
          continue;
        }
        _alreadyGenSourceProduces.add(methodName);
      }
      if (!isImplements && !procedure.isAbstract) {
        continue;
      }

      if (procedure.name.text == 'noSuchMethod') {
        continue;
      }

      String tempContent = _generateProduceSource(procedure);
      buffer.writeln(tempContent);
    }

    for (Field field in clz.fields) {
      if (isPrivateField(field) || field.isStatic) {
        continue;
      }

      methods.add(buildGetField(field));
      if (!field.isFinal && field.isConst) {
        methods.add(buildSetField(field));
      }

      String fieldName = field.name.text;

      if (_alreadyGenSourceFields.contains(fieldName) ||
          _alreadyGenSourceGetProduces.contains(fieldName) ||
          _alreadyGenSourceSetProduces.contains(fieldName)) {
        continue;
      }
      _alreadyGenSourceFields.add(field.name.text);

      String typeStr = _dartTypeToString(field.type);
      buffer.writeln(
          "${typeStr} get ${field.name.text}=>${getParameterValue(field.name.text, field.type.declaredNullability)};");

      if (!field.isFinal && !field.isConst) {
        buffer.writeln(vm_entry_point);
        String paramStr = "${typeStr} ${field.name.text}";
        if (_isAnonymousFunction(field.type)) {
          paramStr =
              "${_dartTypeToString(field.type, funcName: field.name.text)}";
        }
        buffer.writeln(
            "void set ${field.name}(${paramStr}){jsonMap['child']=${field.name.text};}");
      }
    }
    if (!keepClassSource.containsKey(clz) &&
        !isPrivateClass(clz) &&
        !isPrivateLibrary(clz.enclosingLibrary)) {
      methodIndex++;
      String methodName = "${_preMethodName}$methodIndex";
      keepClassInvokeMethodName[clz] = methodName;
      invokeMethodStr =
          "${methodName}(${getParameterValue(clz.name, Nullability.nonNullable)});";
      StringBuffer buffer = new StringBuffer();
      buffer.writeln("void $methodName(${clz.name} ${constructorName}){");
      for (String item in methods) {
        buffer.writeln(item);
      }
      buffer.writeln("}");

      keepClassSource[clz] = buffer.toString();
    }

    return buffer.toString();
  }

  // @param: debugLog
  //    Used to print the methods of BaseTapGestureRecognizer.
  void _generateSuperClassSource(
      Class clz, StringBuffer buffer, bool isImplements,
      {List<List<String>>? typeLists, List<List<DartType>>? typeArguments}) {
    bool isGenerateSource(Class? clz) {
      if (clz != null && !_isObject(clz)) {
        return true;
      }
      return false;
    }

    _getDependenciesLibrary(clz);

    if (typeLists == null) {
      typeLists = [];
    }
    if (typeArguments == null) {
      typeArguments = [];
    }

    if (isGenerateSource(clz.superclass)) {
      String content = "";
      List<String> typeList = <String>[];
      for (TypeParameter item in clz.superclass!.typeParameters) {
        typeList.add(item.name!);
      }
      typeLists.insert(0, typeList);
      typeArguments.insert(0, clz.supertype!.typeArguments);
      runZoned(() {
        content = _generateProcedureAndFieldSource(
            clz.superclass!, isImplements ? true : false);
      }, zoneValues: {#typeArgs: typeArguments, #typeList: typeLists});
      buffer.write(content);
      _generateSuperClassSource(
          clz.superclass!, buffer, isImplements ? true : false,
          typeLists: typeLists, typeArguments: typeArguments);
    }
    if (clz.isMixinDeclaration && !clz.isMixinApplication) {
      String content = "";
      List<String> typeList = <String>[];
      for (TypeParameter item in clz.superclass!.typeParameters) {
        typeList.add(item.name!);
      }
      typeLists.insert(0, typeList);
      typeArguments.insert(0, clz.supertype!.typeArguments);
      runZoned(() {
        content = _generateProcedureAndFieldSource(
            clz.superclass!, isImplements ? true : false);
      }, zoneValues: {#typeArgs: typeArguments, #typeList: typeLists});
      buffer.write(content);
      _generateSuperClassSource(
          clz.superclass!, buffer, isImplements ? true : false,
          typeLists: typeLists, typeArguments: typeArguments);
    }

    if (isGenerateSource(clz.mixedInClass)) {
      String content = "";
      List<String> typeList = <String>[];
      for (TypeParameter item in clz.mixedInClass!.typeParameters) {
        typeList.add(item.name!);
      }
      typeLists.insert(0, typeList);
      typeArguments.insert(0, clz.mixedInType!.typeArguments);
      runZoned(() {
        content = _generateProcedureAndFieldSource(
            clz.mixedInClass!, isImplements ? true : false);
      }, zoneValues: {#typeArgs: typeArguments, #typeList: typeLists});
      buffer.write(content);
      _generateSuperClassSource(
          clz.mixedInClass!, buffer, isImplements ? true : false,
          typeArguments: typeArguments, typeLists: typeLists);
    }
    for (Supertype supertype in clz.implementedTypes) {
      if (isGenerateSource(supertype.classNode) &&
          supertype.classNode.isAbstract) {
        String content = "";
        List<String> typeList = <String>[];
        for (TypeParameter item in supertype.classNode.typeParameters) {
          typeList.add(item.name!);
        }
        typeLists.insert(0, typeList);
        typeArguments.insert(0, supertype.typeArguments);
        runZoned(() {
          content = _generateProcedureAndFieldSource(supertype.classNode,
              isImplements ? true : !supertype.classNode.isMixinDeclaration);
        }, zoneValues: {#typeArgs: typeArguments, #typeList: typeLists});
        buffer.write(content);
        _generateSuperClassSource(supertype.classNode, buffer,
            isImplements ? true : !supertype.classNode.isMixinDeclaration,
            typeArguments: typeArguments, typeLists: typeLists);
      }
    }
  }

  String _generateProduceSource(Procedure procedure) {
    if (procedure.isGetter) {
      return _generateGetProduceSource(procedure);
    } else if (procedure.isSetter) {
      return _generateSetProduceSource(procedure);
    } else {
      return _generateMethodSource(procedure);
    }
  }

  String _generateGetProduceSource(Procedure procedure) {
    StringBuffer procedureBuffer = new StringBuffer();
    DartType returnType = procedure.function.returnType;
    procedureBuffer.writeln(vm_entry_point);

    procedureBuffer.write("${_dartTypeToString(returnType)}");
    procedureBuffer.write(" get ${procedure.name}");
    procedureBuffer.write(
        "=>${getParameterValue(procedure.name.text, returnType.declaredNullability)};");
    return procedureBuffer.toString();
  }

  String _generateSetProduceSource(Procedure procedure) {
    StringBuffer procedureBuffer = new StringBuffer();
    procedureBuffer.writeln(vm_entry_point);
    procedureBuffer.write("set ${procedure.name}(");
    DartType type = procedure.function.positionalParameters[0].type;
    if (_isAnonymousFunction(type)) {
      String funcName = procedure.function.positionalParameters[0].name!;
      if (funcName == "#externalFieldValue") {
        funcName = procedure.name.text + "Handler";
      }
      procedureBuffer.write("${_dartTypeToString(type, funcName: funcName)}");
    } else {
      String funcName = procedure.function.positionalParameters[0].name!;
      if (funcName == "#externalFieldValue") {
        funcName = "value";
      }
      procedureBuffer.write("${_dartTypeToString(type)} "
          "${funcName}");
    }

    procedureBuffer.write("){jsonMap['child']='child';}");
    return procedureBuffer.toString();
  }

  String _getFunctionParameters(FunctionNode function) {
    if (function.requiredParameterCount == 0 &&
        function.positionalParameters.length == 0 &&
        function.namedParameters.length == 0) {
      return "";
    }
    StringBuffer params = new StringBuffer();

    for (int i = 0; i < function.requiredParameterCount; i++) {
      VariableDeclaration variableDeclaration =
          function.positionalParameters[i];

      params.write(_getParameterStr(variableDeclaration));

      if (i != function.requiredParameterCount - 1) {
        params.write(",");
      }
    }

    for (int i = 0; i < function.namedParameters.length; i++) {
      if (i == 0) {
        if (function.requiredParameterCount > 0) {
          params.write(",");
        }
        params.write("{");
      }
      VariableDeclaration variableDeclaration = function.namedParameters[i];
      params.write(_getParameterStr(variableDeclaration, optional: true));

      if (i != function.namedParameters.length - 1) {
        params.write(",");
      }
    }
    if (function.namedParameters.length > 0) {
      params.write("}");
    }

    for (int i = function.requiredParameterCount;
        i < function.positionalParameters.length;
        i++) {
      if (i == function.requiredParameterCount) {
        if (function.requiredParameterCount > 0 ||
            function.namedParameters.length > 0) {
          params.write(",");
        }
        params.write("[");
      }
      VariableDeclaration variableDeclaration =
          function.positionalParameters[i];
      params.write(_getParameterStr(variableDeclaration, optional: true));

      if (i != function.positionalParameters.length - 1) {
        params.write(",");
      }
    }
    if (function.positionalParameters.length - function.requiredParameterCount >
        0) {
      params.write("]");
    }
    String paramsStr = params.toString();
    paramsStr = paramsStr.replaceAll(",,", "");
    paramsStr = paramsStr.replaceAll(",\}", "}");
    paramsStr = paramsStr.replaceAll(",\]", "]");
    if (paramsStr.endsWith(",")) {
      paramsStr = paramsStr.substring(0, paramsStr.length - 1);
    }
    return paramsStr;
  }

  String _generateMethodSource(Procedure procedure) {
    StringBuffer procedureBuffer = new StringBuffer();
    StringBuffer? functionTypeStr;
    List<String> typeParameterNames = [];
    if (procedure.function.typeParameters.length > 0) {
      functionTypeStr = new StringBuffer();
      for (int i = 0; i < procedure.function.typeParameters.length; i++) {
        TypeParameter parameter = procedure.function.typeParameters[i];
        typeParameterNames.add(parameter.name!);
        if (parameter.defaultType is InterfaceType) {
          String type = _dartTypeToString(parameter.defaultType);
          functionTypeStr.write(" ${parameter.name} extends ${type} ");
        } else {
          functionTypeStr.write("${parameter.name}");
        }
        if (i != procedure.function.typeParameters.length - 1) {
          functionTypeStr.write(",");
        }
      }
    }
    runZoned(() {
      String params = _getFunctionParameters(procedure.function);

      DartType type = procedure.function.returnType;

      procedureBuffer.writeln(vm_entry_point);
      procedureBuffer.write(_dartTypeToString(type));
      if (procedure.kind != ProcedureKind.Operator) {
        procedureBuffer.write(" ${procedure.name}");
        if (functionTypeStr != null) {
          procedureBuffer.write("<${functionTypeStr.toString()}>");
        }
        procedureBuffer.write("(");
      } else {
        // handle operator negative
        if (procedure.name.text.startsWith("unary")) {
          procedureBuffer.write(" operator -(");
        } else {
          procedureBuffer.write(" operator ${procedure.name}(");
        }
      }

      procedureBuffer.write("${params}){");

      if (procedure.function.returnType is VoidType) {
        procedureBuffer.write("jsonMap['child']='child';}");
      } else {
        procedureBuffer.write(
            "return ${getParameterValue(procedure.name.text, procedure.function.returnType.declaredNullability)};}");
      }
    }, zoneValues: {
      #functionTypeList: typeParameterNames,
      #typeArgs: Zone.current[#typeArgs],
      #typeList: Zone.current[#typeList]
    });

    return procedureBuffer.toString();
  }

  String _dartTypeToString(DartType dartType, {String? funcName}) {
    List<String> functionTypeList = Zone.current[#functionTypeList];
    List<List<String>> typeLists = Zone.current[#typeList];
    List<List<DartType>> typeArguments = Zone.current[#typeArgs];
    bool nullable = dynamicartNullSafety &&
        dartType.declaredNullability == Nullability.nullable;
    if (dartType is TypeParameterType) {
      TypeParameterType parameterType = dartType;
      String name = "${parameterType.parameter.name}";
      if (functionTypeList != null) {
        if (functionTypeList.contains(name)) {
          return "${name}${nullable ? '?' : ''}";
        }
      }
      if (typeLists != null && typeArguments != null) {
        for (int i = 0; i < typeLists.length; i++) {
          List<String> typeList = typeLists[i];
          int index = typeList.indexOf(name);
          if (index >= 0 && index < typeArguments[i].length) {
            DartType dtype = typeArguments[i][index];
            if (!(dtype is TypeParameterType)) {
              return _dartTypeToString(dtype);
            } else {
              TypeParameterType tptype = dtype as TypeParameterType;
              name = "${tptype.parameter.name}";
            }
          }
        }
      }
      return "${name}${nullable ? '?' : ''}";
    } else if (dartType is FunctionType) {
      FunctionType functionType = dartType;
      StringBuffer types = new StringBuffer();
      if (functionType.typedefReference == null) {
        for (int i = 0; i < functionType.requiredParameterCount; i++) {
          String str = _dartTypeToString(functionType.positionalParameters[i]);
          types.write("${str} index${i}");

          if (i != functionType.requiredParameterCount - 1) {
            types.write(",");
          }
        }
        if (functionType.requiredParameterCount > 0 &&
            functionType.namedParameters.length > 0) {
          types.write(",");
        }
        if (functionType.namedParameters.length > 0) {
          types.write("{");
        }
        for (int i = 0; i < functionType.namedParameters.length; i++) {
          types.write(_dartTypeToString(functionType.namedParameters[i].type));
          types.write(" ${functionType.namedParameters[i].name}");

          if (i != functionType.namedParameters.length - 1) {
            types.write(",");
          }
        }

        if (functionType.namedParameters.length > 0) {
          types.write("}");
        }
        if (functionType.requiredParameterCount > 0 ||
            functionType.namedParameters.length > 0) {
          types.write(",");
        }
        bool hasPositionalParameters =
            functionType.positionalParameters.length -
                    functionType.requiredParameterCount >
                0;
        if (hasPositionalParameters) {
          types.write("[");
        }

        for (int i = functionType.requiredParameterCount;
            i < functionType.positionalParameters.length;
            i++) {
          String str = _dartTypeToString(functionType.positionalParameters[i]);
          types.write("${str} index${i}");
          if (i != functionType.requiredParameterCount - 1) {
            types.write(",");
          }
        }
        if (hasPositionalParameters) {
          types.write("]");
        }
        DartType returnType = functionType.returnType;
        String returnTypeString = _dartTypeToString(returnType);
        if (funcName == null) {
          funcName = "Function";
        }
        return "${returnTypeString} ${funcName}(${types.toString()})${nullable ? '?' : ''}";
      } else {
        if (functionType.typedefReference!.node is Typedef) {
          Typedef typedef = functionType.typedefReference!.asTypedef;
          if (typedef.typeParameters.length > 0) {
            List<DartType?> list =
                new List.filled(typedef.typeParameters.length, null);
            for (int i = 0; i < typedef.typeParameters.length; i++) {
              TypeParameter typeParameter = typedef.typeParameters[i];

              bool isFindType = false;
              for (int j = 0; j < typedef.positionalParameters.length; j++) {
                if (!(typedef.positionalParameters[j].type
                    is TypeParameterType)) {
                  continue;
                }

                TypeParameterType type =
                    typedef.positionalParameters[j].type as TypeParameterType;
                if ((type.parameter.name == typeParameter.name)) {
                  if (j < functionType.positionalParameters.length &&
                      !(functionType.positionalParameters[j]
                          is TypeParameterType)) {
                    isFindType = true;
                    list[i] = functionType.positionalParameters[j];
                    break;
                  }
                }
              }
              if (!isFindType) {
                for (int j = 0; j < typedef.namedParameters.length; j++) {
                  if (!(typedef.namedParameters[j].type is TypeParameterType)) {
                    continue;
                  }

                  TypeParameterType type =
                      typedef.namedParameters[j].type as TypeParameterType;

                  if ((type.parameter.name == typeParameter.name)) {
                    if (j < functionType.namedParameters.length &&
                        !(functionType.positionalParameters[j]
                            is TypeParameterType)) {
                      isFindType = true;
                      list[i] = functionType.namedParameters[j].type;
                      break;
                    }
                  }
                }
              }
            }

            StringBuffer buffer = new StringBuffer();
            buffer.write("<");
            for (int i = 0; i < typedef.typeParameters.length; i++) {
              if (list[i] != null) {
                buffer.write(_dartTypeToString(list[i]!));
              } else {
                buffer.write(typedef.typeParameters[i].name);
              }

              if (i != typedef.typeParameters.length - 1) {
                buffer.write(",");
              }
            }
            buffer.write(">");
            return "${typedef.name}${buffer.toString()}${nullable ? '?' : ''}";
          }
          return "${typedef.name}${nullable ? '?' : ''}";
        }
        return "${functionType.typedefReference?.node?.reference.canonicalName?.name}${nullable ? '?' : ''}";
      }
    } else if (dartType is InterfaceType) {
      InterfaceType interfaceType = dartType;
      StringBuffer buffer = new StringBuffer();

      buffer.write("${interfaceType.classNode.name}");

      if (interfaceType.typeArguments.length > 0) {
        buffer.write("<");
        for (int i = 0; i < interfaceType.typeArguments.length; i++) {
          buffer.write(_dartTypeToString(interfaceType.typeArguments[i]));
          if (i != interfaceType.typeArguments.length - 1) {
            buffer.write(",");
          }
        }

        buffer.write(">");
      }
      if (nullable) {
        buffer.write("?");
      }
      return buffer.toString();
    } else if (dartType is VoidType || dartType is DynamicType) {
      return dartType.bdToString();
    } else if (dartType is FutureOrType) {
      StringBuffer buffer = new StringBuffer();
      FutureOrType futureType = dartType;

      buffer.write("FutureOr");
      if (futureType.typeArgument != null) {
        buffer.write("<");
        buffer.write(_dartTypeToString(futureType.typeArgument));
        buffer.write(">");
      }
      if (nullable) {
        buffer.write("?");
      }
      return buffer.toString();
    } else {
      String str = "${dartType.toString()}${nullable ? '?' : ''}";
      return str;
    }
  }

  String _getParameterStr(VariableDeclaration declaration,
      {bool optional = false}) {
    if (declaration.name!.startsWith("\$creationLocationd")) {
      return "";
    }
    bool nullable = false;
    if (dynamicartNullSafety) {
      nullable =
          declaration.type.declaredNullability == Nullability.nonNullable &&
              optional;
    }
    StringBuffer buffer = new StringBuffer();
    if (declaration.type is FunctionType) {
      FunctionType functionType = declaration.type as FunctionType;
      if (functionType.typedefReference != null) {
        buffer.write(
            "${_dartTypeToString(declaration.type)}${nullable ? '?' : ''} ${declaration.name}");
      } else {
        buffer.write(
            "${_dartTypeToString(declaration.type, funcName: declaration.name)}${nullable ? '?' : ''}");
      }
    } else {
      buffer.write(
          "${_dartTypeToString(declaration.type)}${nullable ? '?' : ''} ${declaration.name}");
    }
    return buffer.toString();
  }

  bool _isAnonymousFunction(DartType type) {
    if (type is FunctionType) {
      FunctionType functionType = type;
      if (functionType.typedefReference == null) {
        return true;
      }
    }
    return false;
  }

  void _getDependenciesLibrary(Class clz) {
    dependencyLibs.add(clz.enclosingLibrary);
    for (LibraryDependency dependency in clz.enclosingLibrary.dependencies) {
      dependencyLibDependencys.add(dependency);
    }
  }
}

String _getClassTypeParametersStr(String source) {
  int startIndex = source.indexOf("<");
  int count = 0;
  for (int i = startIndex; i < source.length; i++) {
    int item = source.codeUnitAt(i);
    if (item == '>'.codeUnitAt(0)) {
      count--;
      if (count == 0) {
        return source.substring(startIndex, i + 1);
      }
    } else if (item == '<'.codeUnitAt(0)) {
      count++;
    }
  }
  return '';
}

bool _isObject(Class clz) {
  if (getPackageName(clz.enclosingLibrary) == "dart:core" &&
      clz.name == "Object") {
    return true;
  }
  return false;
}
