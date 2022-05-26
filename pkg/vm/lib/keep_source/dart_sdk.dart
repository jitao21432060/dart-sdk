import 'package:vm/keep_source/utils.dart';

import 'base.dart';
import 'package:kernel/ast.dart';
import 'package:front_end/src/api_unstable/vm.dart' show CompilerOptions;

class DartLibraryProducer extends SourceProducer {
  Map<String, String> _badCaseKeepMap = {
    "dart:collection": _collectionBadCaseContent,
  };

  List<String> noKeepClzList = [
    "BigInt",
    "num",
    "Uri",
    "int",
    "double",
    "String",
    "Zone",
  ];
  Set<Library> dependLibs = Set();

  String importUri;

  DartLibraryProducer(Uri source, CompilerOptions options, this.importUri,
      Component component, Map<Class, Class> map)
      : super(source, options, component, map);

  @override
  bool canProcessLibrary(Library lib) {
    if (importUri == getPackageName(lib)) {
      // addDependencies(lib);
      return true;
    }

    return false;
  }

  @override
  String getImportUri() {
    return "";
  }

  @override
  String getContent() {
    StringBuffer content = new StringBuffer();
    if (_badCaseKeepMap.containsKey(importUri)) {
      content.write(_badCaseKeepMap[importUri]);
    }
    content.write(super.getContent());

    return content.toString();
  }

  @override
  bool isGenerateSubClassSource(Class clz) {
    if (isDartSDK(clz.enclosingLibrary)) {
      if (noKeepClzList.contains(clz.name)) {
        return false;
      }
    }
    return true;
  }

  @override
  bool canProcessClass(Class clz) {
    if (importUri == "dart:collection" && clz.name == "LinkedList") {
      return false;
    }
    return super.canProcessClass(clz);
  }
}

String _collectionBadCaseContent = """
// import 'dart:typed_data'; 
//    @pragma("vm:entry-point")
//   class TestLinkedListEntry extends LinkedListEntry<TestLinkedListEntry> {
//   @override
//    @pragma("vm:entry-point")
//   LinkedList<TestLinkedListEntry> get list {
//     return super.list;
//   }
//
//   @override
//    @pragma("vm:entry-point")
//   void insertBefore(TestLinkedListEntry entry) {
//     return super.insertBefore(entry);
//   }
//
//   @override
//    @pragma("vm:entry-point")
//   void insertAfter(TestLinkedListEntry entry) {
//     return super.insertAfter(entry);
//   }
//
//   @override
//    @pragma("vm:entry-point")
//   TestLinkedListEntry get previous {
//     return super.previous;
//   }
//
//   @override
//    @pragma("vm:entry-point")
//   TestLinkedListEntry get next {
//     return super.next;
//   }
//
//   @override
//    @pragma("vm:entry-point")
//   void unlink() {
//     return super.unlink();
//   }
// }
// @pragma("vm:entry-point")
// void bad_case_state(){
//  {
//   void aot_keep_vm_entry_point1(LinkedList _construct){
// _construct.addFirst(aot_keep_vm_entry_point_transform(jsonMap['child']));
// _construct.add(aot_keep_vm_entry_point_transform(jsonMap['child']));
// _construct.addAll(aot_keep_vm_entry_point_transform(jsonMap['child']));
// print("\${_construct.remove(aot_keep_vm_entry_point_transform(jsonMap['child']))}");
// print("\${_construct.iterator}");
// print("\${_construct.length}");
// _construct.clear();
// print("\${_construct.first}");
// print("\${_construct.last}");
// print("\${_construct.single}");
// _construct.forEach(aot_keep_vm_entry_point_transform(jsonMap['child']));
// print("\${_construct.isEmpty}");
// }
// aot_keep_vm_entry_point1(LinkedList<TestLinkedListEntry>());
// }
// }
  """;
