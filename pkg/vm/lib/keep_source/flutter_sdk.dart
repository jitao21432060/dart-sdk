import 'package:front_end/src/api_unstable/vm.dart' show CompilerOptions;
import 'package:kernel/ast.dart';
import 'base.dart';
import 'constant.dart';
import 'utils.dart';

class FlutterLibraryProducer extends SourceProducer {
  FlutterLibraryProducer(Uri source, CompilerOptions options,
      Component component, Map<Class, Class> map)
      : super(source, options, component, map);

  @override
  bool canProcessLibrary(Library lib) {
    String packageName = getPackageName(lib);
    if (packageName.contains("bitfield_unsupported.dart")) {
      return false;
    }

    return isInKeepFlutterSDK(lib);
  }

  @override
  String getImportUri() {
    StringBuffer content = new StringBuffer();

    content.writeln("${importCommonUri}");
    return content.toString();
  }
}
