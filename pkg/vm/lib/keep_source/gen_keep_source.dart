import 'dart:collection';
import 'dart:io';

import 'package:front_end/src/api_unstable/vm.dart'
    show CompilerOptions, CompilerResult;
import 'package:kernel/ast.dart';
import 'package:kernel/core_types.dart';
import 'package:kernel/library_index.dart';
import 'package:vm/metadata/inferred_type.dart';
import '../kernel_front_end.dart';
import 'base.dart';
import 'constant.dart';
import 'dart_sdk.dart';
import 'dyamic_aot_plugins.dart';
import 'flutter_sdk.dart';
import 'parsed_package.dart';
import 'utils.dart';
import 'package:kernel/ast.dart' show Component;
import 'package:front_end/src/api_unstable/vm.dart'
    show kernelForProgram, kernelForPrograms;
import 'package:front_end/src/base/nnbd_mode.dart';
import 'package:front_end/src/base/processed_options.dart';
import 'package:yaml/yaml.dart' as yaml;

late File commonFile;
bool toB = false;

List<Uri> _getKeepSources(Uri source, CompilerOptions options) {
  List<Uri> _getImportUris(String directoryPath, String packagePrefix) {
    List<Uri> imports = <Uri>[];
    Directory directory = Directory(directoryPath);
    if (!directory.existsSync()) {
      return imports;
    }
    List<FileSystemEntity> list =
        directory.listSync(recursive: true, followLinks: false);
    for (FileSystemEntity entity in list) {
      if (entity.path.endsWith(".dart") && !entity.path.endsWith("_web.dart")) {
        imports.add(Uri.parse(
            packagePrefix + entity.path.substring(directoryPath.length + 1)));
      }
    }
    return imports;
  }

  List<Uri> sources = <Uri>[];
  sources.add(source);
  sources.addAll(keepPackageNames);
  Map<String, String> map =
      parsePackage(options.fileSystem, options.packagesFileUri!);
  sources.addAll(_getImportUris(map["flutter"]!, "package:flutter/"));
  for (String key in map.keys) {
    String packageName = "package:${key}/";
    if (options.dynamicAotLibs != null) {
      for (String item in options.dynamicAotLibs!) {
        if (item.startsWith(packageName)) {
          String subdir = item.substring(packageName.length);
          if (subdir.isNotEmpty) {
            subdir = "/" + subdir;
            if (subdir.endsWith("/")) {
              subdir = subdir.substring(0, subdir.length - 1);
            }
          }
          sources.addAll(_getImportUris(map[key]! + subdir, item));
        }
      }
    }
  }
  return sources;
}

Future<CompilerResult?> compileDynamicart(
    Uri source, CompilerOptions options, bool aot, CompilerResult result,
    {bool? dynamicart}) async {
  result = (await kernelForPrograms(_getKeepSources(source, options), options,
      dynamicart: dynamicart))!;

  if (result.component == null) {
    return null;
  }

  if (!aot) {
    return result;
  }

  final errorDetector =
      new ErrorDetector(previousErrorHandler: options.onDiagnostic);
  options.onDiagnostic = errorDetector;

  // set dynamicart nullsafety mode
  String? sdkVersion = null;
  final pubspecNode = yaml.loadYaml(
    File.fromUri(Uri.file("pubspec.yaml")).readAsStringSync(),
  );
  final yaml.YamlMap environment = pubspecNode['environment'];
  if (environment != null && environment is yaml.YamlMap) {
    for (String key in environment.keys) {
      print("yaml key is:${key}");
      if (key == "sdk") {
        sdkVersion = environment[key].toString();
      }
    }
  }
  if (sdkVersion != null) {
    String versionSplit = sdkVersion.split('>=')[1];
    String major = versionSplit.split('.')[0];
    String minor = versionSplit.split('.')[1];
    if (int.parse(major) >= 2 && int.parse(minor) >= 12) {
      dynamicartNullSafety = true;
    }
  }
  print("dynamicartNullSafety mode is:${dynamicartNullSafety}");

  List<Uri> sources = _genKeepSourceUri(source, options, result.component!);

  result = (await kernelForPrograms(sources, options, dynamicart: dynamicart))!;

  _addEntryPointAnnotationForKeepDartPrivate(result.component!);
  _clean(options);
  return result;
}

Future<CompilerResult?> compileHotUpdateHost(
    Uri source, CompilerOptions options, bool aot, CompilerResult result,
    {bool enableAsserts: true,
    bool useGlobalTypeFlowAnalysis: false,
    bool useProtobufTreeShakerV2: false,
    bool minimalKernel: false,
    bool treeShakeWriteOnlyFields: false,
    bool? dynamicart}) async {
  List<Uri> uris = [];
  uris.add(source);
  result = (await kernelForPrograms(uris, options, dynamicart: dynamicart))!;
  if (result.component == null) {
    return null;
  }
  final errorDetector =
      new ErrorDetector(previousErrorHandler: options.onDiagnostic);
  options.onDiagnostic = errorDetector;
  bool shouldContinue = true;
  Set<String> alreadyKeepClasses = HashSet();
  Component? tmpComponent = null;
  while (shouldContinue) {
    options.diffTarget = createFrontEndTarget(
      'flutter',
      trackWidgetCreation: true,
      nullSafety: options.nnbdMode == NnbdMode.Strong,
    );
    await runGlobalTransformations(
        options.diffTarget!,
        result.component!,
        useGlobalTypeFlowAnalysis,
        enableAsserts,
        useProtobufTreeShakerV2,
        errorDetector,
        minimalKernel: minimalKernel,
        treeShakeWriteOnlyFields: treeShakeWriteOnlyFields,
        dynamicart: true,
        hostDillComponent: options.hostDillComponent);
    if (options.hotUpdateHostDillComponent == null) {
      options.hotUpdateHostDillComponent = result.component;
    }
    tmpComponent = result.component;
    result = (await kernelForPrograms(uris, options, dynamicart: dynamicart))!;
    shouldContinue = _addEntryPointAnnotationForKeepField(
        result.component!, options, tmpComponent!, alreadyKeepClasses);
  }

  // set dynamicart nullsafety mode
  String? sdkVersion = null;
  final pubspecNode = yaml.loadYaml(
    File.fromUri(Uri.file("pubspec.yaml")).readAsStringSync(),
  );
  final yaml.YamlMap environment = pubspecNode['environment'];
  if (environment != null && environment is yaml.YamlMap) {
    for (String key in environment.keys) {
      print("yaml key is:${key}");
      if (key == "sdk") {
        sdkVersion = environment[key].toString();
      }
    }
  }
  if (sdkVersion != null) {
    String versionSplit = sdkVersion.split('>=')[1];
    String major = versionSplit.split('.')[0];
    String minor = versionSplit.split('.')[1];
    if (int.parse(major) >= 2 && int.parse(minor) >= 12) {
      dynamicartNullSafety = true;
    }
  }
  print("dynamicartNullSafety mode is:${dynamicartNullSafety}");

  result = (await kernelForPrograms(_getKeepSources(source, options), options,
      dynamicart: dynamicart))!;

  List<Uri> sources = _genKeepSourceUri(source, options, result.component!);
  result = (await kernelForPrograms(sources, options, dynamicart: dynamicart))!;

  _addEntryPointAnnotationForKeepDartPrivate(result.component!);
  _addEntryPointAnnotationForKeepField(
      result.component!, options, tmpComponent!, alreadyKeepClasses);
  _clean(options);
  return result;
}

Future<CompilerResult> compileDynamicDill(
    Uri source, CompilerOptions options, bool aot, CompilerResult result,
    {bool? dynamicart}) async {
  List<Uri> uris = [];
  uris.add(source);

  result = (await kernelForPrograms(uris, options, dynamicart: dynamicart))!;

  for (Library library in result.component!.libraries) {
    String packageName = "${library.importUri}";

    if (isDynamicLib(library, options) &&
        !packageName.startsWith("package:flutter/")) {
      library.importUri =
          Uri.parse("package:fix_" + packageName.substring("package:".length));
    }
  }
  return result;
}

Future<CompilerResult?> compileHotUpdatePackage(
    Uri source, CompilerOptions options, bool aot, CompilerResult result,
    {bool enableAsserts: true,
    bool useGlobalTypeFlowAnalysis: false,
    bool useProtobufTreeShakerV2: false,
    bool minimalKernel: false,
    bool treeShakeWriteOnlyFields: false,
    bool? dynamicart}) async {
  List<Uri> uris = [];
  uris.add(source);

  result = (await kernelForPrograms(uris, options, dynamicart: dynamicart))!;
  if (result.component == null) {
    return null;
  }
  return result;
}

Future<CompilerResult> compile(
  Uri source,
  CompilerOptions options,
  bool aot, {
  bool enableAsserts: true,
  bool useGlobalTypeFlowAnalysis: false,
  bool useProtobufTreeShakerV2: false,
  bool minimalKernel: false,
  bool treeShakeWriteOnlyFields: false,
}) async {
  CompilerResult result = (await kernelForProgram(source, options))!;

  if (options.dynamicart) {
    if (options.hotUpdate) {
      result = (await compileHotUpdateHost(source, options, aot, result,
          enableAsserts: enableAsserts,
          useGlobalTypeFlowAnalysis: useGlobalTypeFlowAnalysis,
          useProtobufTreeShakerV2: useProtobufTreeShakerV2,
          minimalKernel: minimalKernel,
          treeShakeWriteOnlyFields: treeShakeWriteOnlyFields,
          dynamicart: true))!;
    } else {
      result = (await compileDynamicart(source, options, aot, result,
          dynamicart: true))!;
    }
  } else if (options.dynamicdill) {
    if (options.hotUpdate) {
      result = (await compileHotUpdatePackage(source, options, aot, result,
          enableAsserts: enableAsserts,
          useGlobalTypeFlowAnalysis: useGlobalTypeFlowAnalysis,
          useProtobufTreeShakerV2: useProtobufTreeShakerV2,
          minimalKernel: minimalKernel,
          treeShakeWriteOnlyFields: treeShakeWriteOnlyFields,
          dynamicart: true))!;
    } else {
      result = await compileDynamicDill(source, options, aot, result,
          dynamicart: true);
    }
  }
  return result;
}

List<Uri> _genKeepSourceUri(
    Uri source, CompilerOptions options, Component component) {
  String packagesFileUri = options.packagesFileUri!.toFilePath();
  int index = packagesFileUri.lastIndexOf("/");
  String directory = packagesFileUri.substring(0, index);
  commonFile =
      new File("${directory}/../lib/${aotKeepVmEntryPointFileName}.dart");
  commonFile.writeAsStringSync(commonContent);

  Map<Class, Class> map = new Map();
  for (Library library in component.libraries) {
    for (Class clz in library.classes) {
      if (isPrivateClass(clz)) {
        continue;
      }
      if (!isDynamicLib(library, options)) {
        _genSubClassMap(clz, clz, map);
      }
    }
  }
  List<SourceProducer> list =
      _createSourceProducer(source, options, component, map);
  for (Library library in component.libraries) {
    for (SourceProducer producer in list) {
      if (producer.canProcessLibrary(library)) {
        producer.processLibrary(library);
      }
    }
  }

  String packageName = source.path.substring(0, source.path.lastIndexOf("/"));
  List<Uri> sources = <Uri>[];
  sources.add(source);
  for (SourceProducer producer in list) {
    List<String> fileNames = producer.getFileNames();
    fileNames.forEach((filename) {
      sources.add(Uri.parse("package:${packageName}/${filename}"));
    });
  }
  return sources;
}

void _clean(CompilerOptions options) {
  Directory? buildDirectory;
  if (options.outputPath != null) {
    File file = new File(options.outputPath!);
    buildDirectory = file.parent;
  }

  for (SourceProducer producer in producers!) {
    var files = producer.getFiles();
    var fileNames = producer.getFileNames();
    if (buildDirectory != null) {
      for (int i = 0; i < fileNames.length; i++) {
        File outputFile = new File(
            buildDirectory.path + Platform.pathSeparator + fileNames[i]);
        outputFile.writeAsStringSync(files[i].readAsStringSync());
        files[i].deleteSync();
      }
    }
  }
  if (buildDirectory != null) {
    File file = new File(buildDirectory.path +
        Platform.pathSeparator +
        aotKeepVmEntryPointFileName +
        ".dart");
    file.writeAsStringSync(commonFile.readAsStringSync());
  }
  commonFile.deleteSync();
}

List<SourceProducer>? producers;

List<SourceProducer> _createSourceProducer(Uri source, CompilerOptions options,
    Component component, Map<Class, Class> map) {
  if (producers == null) {
    producers = <SourceProducer>[];
    for (String item in dartPackageNames) {
      producers
          ?.add(DartLibraryProducer(source, options, item, component, map));
    }
    producers?.add(FlutterLibraryProducer(source, options, component, map));
    List<String>? dynamicAotLib = options.dynamicAotLibs;
    if (dynamicAotLib != null) {
      for (String item in dynamicAotLib) {
        producers?.add(
            DynamicLibraryProducer(source, options, item, component, map));
      }
    }
  }
  return producers!;
}

bool isDynamicLib(Library lib, CompilerOptions options) {
  if (isInKeepFlutterSDK(lib) || isDartSDK(lib)) {
    return false;
  }

  List<String>? dynamicAotLib = options.dynamicAotLibs;
  if (dynamicAotLib != null) {
    for (String item in dynamicAotLib) {
      if ("${lib.importUri}".startsWith(item) && item.isNotEmpty) {
        return false;
      }
    }
  }
  return true;
}

bool checkParameters(
    FunctionNode function, Map<String, MetadataRepository<Object>> metadata) {
  bool checkMetaData(VariableDeclaration node) {
    if (node.name!.contains("creationLocation")) {
      return false;
    }
    for (var md in metadata.values) {
      final nodeMetadata = md.mapping[node];
      if (nodeMetadata != null && nodeMetadata is InferredType) {
        if (nodeMetadata.constantValue != null) {
          return true;
        }
      }
    }
    return false;
  }

  int count = function.positionalParameters.length;
  for (int i = 0; i < count; i++) {
    if (checkMetaData(function.positionalParameters[i])) {
      return true;
    }
  }
  count = function.namedParameters.length;
  for (int i = 0; i < count; i++) {
    if (checkMetaData(function.namedParameters[i])) {
      return true;
    }
  }
  return false;
}

bool _annotationsDefineRoot(CoreTypes coreTypes, List<Expression> annotations) {
  for (var annotation in annotations) {
    InstanceConstant? pragmaConstant = null;
    if (annotation is ConstantExpression) {
      Constant constant = annotation.constant;
      if (constant is InstanceConstant) {
        if (constant.classNode == coreTypes.pragmaClass) {
          pragmaConstant = constant;
        }
      }
    }
    if (pragmaConstant == null) {
      continue;
    }

    String pragmaName;
    Constant name =
        pragmaConstant.fieldValues[coreTypes.pragmaName.getterReference]!;
    if (name is StringConstant) {
      pragmaName = name.value;
    } else {
      continue;
    }
    const kEntryPointPragmaName = "vm:entry-point";
    if (pragmaName == kEntryPointPragmaName) {
      return true;
    }
  }
  return false;
}

void _addEntryPointAnnotationForKeepFunction(Component component,
    CompilerOptions options, Component keepClassComponent) {
  final coreTypes = new CoreTypes(component);
  Map<Reference, Constant> map = new Map();
  map[coreTypes.pragmaName.reference] = StringConstant("vm:entry-point");
  map[coreTypes.pragmaOptions.reference] = NullConstant();
  LibraryIndex keepClassComponentIndexer = LibraryIndex.all(keepClassComponent);
  for (Library library in component.libraries) {
    if (!toB && !isDynamicLib(library, options)) {
      continue;
    }

    Library? diffLibrary =
        keepClassComponentIndexer.tryGetLibrary(library.importUri.toString());
    if (diffLibrary == null) {
      continue;
    }

    if (diffLibrary.fields.isEmpty &&
        diffLibrary.procedures.isEmpty &&
        diffLibrary.classes.isEmpty) {
      continue;
    }

    String getDisambiguatedName(Member member) {
      if (member is Procedure) {
        if (member.isGetter)
          return LibraryIndex.getterPrefix + member.name.text;
        if (member.isSetter)
          return LibraryIndex.setterPrefix + member.name.text;
      }
      return member.name.text;
    }

    for (Procedure procedure in library.procedures) {
      String pname = getDisambiguatedName(procedure);
      Member? member = keepClassComponentIndexer?.tryGetTopLevelMember(
          library.importUri.toString(), LibraryIndex.topLevel, pname);
      if (member == null) {
        continue;
      }
      int paramsCount = member.function!.positionalParameters.length +
          member.function!.namedParameters.length;
      if (paramsCount == 0) {
        continue;
      }
      if (!checkParameters(
          member.function!,
          keepClassComponent.metadata
              as Map<String, MetadataRepository<Object>>)) {
        continue;
      }
      if (!_annotationsDefineRoot(coreTypes, procedure.annotations)) {
        procedure.addAnnotation(ConstantExpression(InstanceConstant(
            coreTypes.pragmaClass.reference, <DartType>[], map)));
      }
    }

    for (Class clz in library.classes) {
      Class? c = keepClassComponentIndexer.tryGetClass(
          library.importUri.toString(), clz.name);
      if (c == null) {
        continue;
      }
      for (Constructor construct in clz.constructors) {
        String pname = getDisambiguatedName(construct);
        Member? member = keepClassComponentIndexer?.tryGetMember(
            library.importUri.toString(), clz.name, pname);
        if (member == null) {
          continue;
        }
        int paramsCount = member.function!.positionalParameters.length +
            member.function!.namedParameters.length;
        if (paramsCount == 0) {
          continue;
        }
        if (!checkParameters(
            member.function!,
            keepClassComponent.metadata
                as Map<String, MetadataRepository<Object>>)) {
          continue;
        }
        if (!clz.isAbstract &&
            !_annotationsDefineRoot(coreTypes, construct.annotations)) {
          construct.addAnnotation(ConstantExpression(InstanceConstant(
              coreTypes.pragmaClass.reference, <DartType>[], map)));
        }
      }

      for (Procedure procedure in clz.procedures) {
        String pname = getDisambiguatedName(procedure);
        Member? member = keepClassComponentIndexer?.tryGetMember(
            library.importUri.toString(), clz.name, pname);
        if (member == null) {
          continue;
        }
        int paramsCount = member.function!.positionalParameters.length +
            member.function!.namedParameters.length;
        if (paramsCount == 0) {
          continue;
        }
        if (!checkParameters(
            member.function!,
            keepClassComponent.metadata
                as Map<String, MetadataRepository<Object>>)) {
          continue;
        }
        if (!procedure.isRedirectingFactory &&
            !_annotationsDefineRoot(coreTypes, procedure.annotations)) {
          procedure.addAnnotation(ConstantExpression(InstanceConstant(
              coreTypes.pragmaClass.reference, <DartType>[], map)));
        }
      }
    }
  }
}

bool _addEntryPointAnnotationForKeepField(
    Component component,
    CompilerOptions options,
    Component diffComponent,
    Set<String> alreadyKeepClasses) {
  final coreTypes = new CoreTypes(component);
  Map<Reference, Constant> map = new Map();
  map[coreTypes.pragmaName.reference] = StringConstant("vm:entry-point");
  map[coreTypes.pragmaOptions.reference] = NullConstant();
  LibraryIndex diffComponentIndexer = LibraryIndex.all(diffComponent);
  bool newAdd = false;

  for (Library library in component.libraries) {
    if (!isDynamicLib(library, options)) {
      continue;
    }

    Library? diffLibrary =
        diffComponentIndexer.tryGetLibrary(library.importUri.toString());
    if (diffLibrary == null) {
      continue;
    }

    if (diffLibrary.fields.isEmpty &&
        diffLibrary.procedures.isEmpty &&
        diffLibrary.classes.isEmpty) {
      continue;
    }

    for (Field field in library.fields) {
      if (!_annotationsDefineRoot(coreTypes, field.annotations)) {
        field.addAnnotation(ConstantExpression(InstanceConstant(
            coreTypes.pragmaClass.reference, <DartType>[], map)));
      }
    }

    for (Class clz in library.classes) {
      Class? c = diffComponentIndexer.tryGetClass(
          library.importUri.toString(), clz.name);
      if (c == null) {
        continue;
      }
      String key = "${library.importUri}_${clz.name}";
      if (!alreadyKeepClasses.contains(key)) {
        alreadyKeepClasses.add(key);
        newAdd = true;
      }
      for (Field field in clz.fields) {
        if (!field.name.text.startsWith("_redirecting#") &&
            !_annotationsDefineRoot(coreTypes, field.annotations)) {
          field.addAnnotation(ConstantExpression(InstanceConstant(
              coreTypes.pragmaClass.reference, <DartType>[], map)));
        }
      }
    }
  }
  return newAdd;
}

void _addEntryPointAnnotationForKeepDartPrivate(Component component) {
  final coreTypes = new CoreTypes(component);
  Map<Reference, Constant> map = new Map();
  map[coreTypes.pragmaName.reference] = StringConstant("vm:entry-point");
  map[coreTypes.pragmaOptions.reference] = NullConstant();

  for (Library library in component.libraries) {
    if (!_isKeepPrivateMethod("${library.importUri}")) {
      continue;
    }
    bool isPrivateLib = isPrivateLibrary(library);

    for (Procedure procedure in library.procedures) {
      if (!isPrivateLib && !isPrivateProcedure(procedure)) {
        continue;
      }
      procedure.addAnnotation(ConstantExpression(InstanceConstant(
          coreTypes.pragmaClass.reference, <DartType>[], map)));
    }
    for (Field field in library.fields) {
      if (!isPrivateLib && !isPrivateField(field)) {
        continue;
      }
      field.addAnnotation(ConstantExpression(InstanceConstant(
          coreTypes.pragmaClass.reference, <DartType>[], map)));
    }

    for (Class clz in library.classes) {
      if (clz.name.contains("Deprecated")) {
        continue;
      }
      bool clsPrivate = isPrivateClass(clz);
      for (Constructor construct in clz.constructors) {
        if (!isPrivateLib &&
            !clsPrivate &&
            !isPrivateConstructor(construct) &&
            clz.name != "Object") {
          continue;
        }
        if (!clz.isAbstract) {
          construct.addAnnotation(ConstantExpression(InstanceConstant(
              coreTypes.pragmaClass.reference, <DartType>[], map)));
        }
      }

      for (Field field in clz.fields) {
        if (!isPrivateLib && !clsPrivate && !isPrivateField(field)) {
          continue;
        }
        if (!field.name.text.startsWith("_redirecting#")) {
          field.addAnnotation(ConstantExpression(InstanceConstant(
              coreTypes.pragmaClass.reference, <DartType>[], map)));
        }
      }
      for (Procedure procedure in clz.procedures) {
        if (!isPrivateLib && !clsPrivate && !isPrivateProcedure(procedure)) {
          continue;
        }
        if (!procedure.isRedirectingFactory) {
          procedure.addAnnotation(ConstantExpression(InstanceConstant(
              coreTypes.pragmaClass.reference, <DartType>[], map)));
        }
      }
    }
  }
}

bool _isKeepPrivateMethod(String packageName) {
  if (packageName == "dart:ui" ||
      packageName == "dart:async" ||
      packageName == "dart:core" ||
      packageName == "dart:_http" ||
      packageName == "dart:collection" ||
      packageName == "dart:math") {
    return true;
  }
  return false;
}

void _genSubClassMap(Class clz, Class instanceClass, Map<Class, Class> map) {
  if (clz == null || instanceClass == null || map == null) {
    return;
  }

  Class? superClass = clz.superclass;
  if (superClass != null) {
    map[superClass] = instanceClass;
    _genSubClassMap(superClass, instanceClass, map);
  }
  Class? mixedInClass = clz.mixedInClass;
  if (mixedInClass != null) {
    map[mixedInClass] = instanceClass;
    _genSubClassMap(mixedInClass, instanceClass, map);
  }

  List<Supertype> implementedTypes = clz.implementedTypes;
  for (Supertype supertype in implementedTypes) {
    if (supertype.classNode != null) {
      map[supertype.classNode] = instanceClass;
      _genSubClassMap(supertype.classNode, instanceClass, map);
    }
  }
}
