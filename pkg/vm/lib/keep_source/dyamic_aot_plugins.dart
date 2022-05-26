import 'package:front_end/src/api_unstable/vm.dart' show CompilerOptions;
import 'package:kernel/ast.dart';
import 'base.dart';
import 'constant.dart';
import 'utils.dart';

class DynamicLibraryProducer extends SourceProducer {
  String packageName;

  DynamicLibraryProducer(Uri source, CompilerOptions options, this.packageName,
      Component component, Map<Class, Class> map)
      : super(source, options, component, map);

  @override
  bool canProcessLibrary(Library lib) {
    String libPackageName = getPackageName(lib);
    return libPackageName.startsWith(packageName);
  }

  @override
  String getImportUri() {
    return importCommonUri;
  }
}
