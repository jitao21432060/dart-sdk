import 'package:front_end/src/api_unstable/vm.dart' show FileSystem;

import 'dart:io';
import 'dart:convert';

const int SLASH = 0x2f;
const PERIOD = 0x2e;
const Utf8Codec utf8 = Utf8Codec();
Map<String, String> parsePackage(FileSystem fileSystem, Uri packagesUri) {
  final Map<String, String> map = Map();
  final File dotPackages =
      File(fileSystem.entityForUri(packagesUri).uri.toFilePath());
  final data = utf8.decode(dotPackages.readAsBytesSync());
  final Map packageJson = json.decode(data);
  final List packages = packageJson['packages'] ?? [];
  for (final Map package in packages) {
    String rootUri = package['rootUri'];
    if (!rootUri.endsWith('/')) rootUri += '/';
    final String packageName = package['name'];
    final String packageUri = package['packageUri'];
    final Uri resolvedRootUri = packagesUri.resolve(rootUri);
    final Uri resolvedPackageUri = packageUri != null
        ? resolvedRootUri.resolve(packageUri)
        : resolvedRootUri;
    if (packageUri != null &&
        !'$resolvedPackageUri'.contains('$resolvedRootUri')) {
      throw 'The resolved "packageUri" is not a subdirectory of the "rootUri".';
    }
    String packagePath = resolvedPackageUri
        .toString()
        .substring(7, resolvedPackageUri.toString().length - 1);
    map[packageName] = packagePath;
  }
  return map;
}

String _absolute(String current, String part1,
    [String? part2,
    String? part3,
    String? part4,
    String? part5,
    String? part6,
    String? part7]) {
  //
  _validateArgList(
      "absolute", [part1, part2, part3, part4, part5, part6, part7]);

  // If there's a single absolute path, just return it. This is a lot faster
  // for the common case of `p.absolute(path)`.
  if (part2 == null && (_rootLength(part1) > 0)) {
    return part1;
  }

  return _join(current, part1, part2, part3, part4, part5, part6, part7);
}

String _join(String part1,
    [String? part2,
    String? part3,
    String? part4,
    String? part5,
    String? part6,
    String? part7,
    String? part8]) {
  var parts = <String?>[part1, part2, part3, part4, part5, part6, part7, part8];
  _validateArgList("join", parts);
  return joinAll((parts.where((part) => part != null)) as Iterable<String>);
}

String joinAll(Iterable<String> parts) {
  var buffer = new StringBuffer();
  var needsSeparator = false;

  for (var part in parts.where((part) => part != '')) {
    if (_rootLength(part) > 0) {
      buffer.clear();
      buffer.write(part);
    } else {
      if (part.length > 0 && part[0].contains('/')) {
      } else if (needsSeparator) {
        buffer.write('/');
      }

      buffer.write(part);
    }

    needsSeparator = _needsSeparator(part);
  }

  return buffer.toString();
}

bool _needsSeparator(String path) =>
    path.isNotEmpty && !_isSeparator(path.codeUnitAt(path.length - 1));

void _validateArgList(String method, List<String?> args) {
  for (var i = 1; i < args.length; i++) {
    // Ignore nulls hanging off the end.
    if (args[i] == null || args[i - 1] != null) continue;

    int numArgs;
    for (numArgs = args.length; numArgs >= 1; numArgs--) {
      if (args[numArgs - 1] != null) break;
    }

    // Show the arguments.
    var message = new StringBuffer();
    message.write("$method(");
    message.write(args
        .take(numArgs)
        .map((arg) => arg == null ? "null" : '"$arg"')
        .join(", "));
    message.write("): part ${i - 1} was null, but part $i was not.");
    throw new ArgumentError(message.toString());
  }
}

int _rootLength(String path, {bool withDrive: false}) {
  if (path.isNotEmpty && _isSeparator(path.codeUnitAt(0))) return 1;
  return 0;
}

bool _isSeparator(int codeUnit) => codeUnit == SLASH;

String _normalize(String path) {
  if (!_needsNormalization(path)) return path;

  var parsed = _ParsedPath.parse(path);
  parsed.normalize();
  return parsed.toString();
}

bool _needsNormalization(String path) {
  var start = 0;
  var codeUnits = path.codeUnits;
  int? previousPrevious;
  int? previous;

  var root = _rootLength(path);
  if (root != 0) {
    start = root;
    previous = SLASH;
  }

  for (var i = start; i < codeUnits.length; i++) {
    var codeUnit = codeUnits[i];
    if (_isSeparator(codeUnit)) {
      if (previous != null && _isSeparator(previous)) return true;

      if (previous == PERIOD &&
          (previousPrevious == null ||
              previousPrevious == PERIOD ||
              _isSeparator(previousPrevious))) {
        return true;
      }
    }

    previousPrevious = previous;
    previous = codeUnit;
  }

  if (previous == null) return true;

  if (_isSeparator(previous)) return true;

  // Single dots and double dots are normalized to directory traversals.
  if (previous == PERIOD &&
      (previousPrevious == null ||
          _isSeparator(previousPrevious) ||
          previousPrevious == PERIOD)) {
    return true;
  }

  return false;
}

class _ParsedPath {
  String root;

  bool isRootRelative;

  /// The path-separated parts of the path. All but the last will be
  /// directories.
  List<String> parts;

  /// The path separators preceding each part.
  ///
  /// The first one will be an empty string unless the root requires a separator
  /// between it and the path. The last one will be an empty string unless the
  /// path ends with a trailing separator.
  List<String> separators;

  /// The file extension of the last non-empty part, or "" if it doesn't have
  /// one.
  String get extension => _splitExtension()[1];

  /// `true` if this is an absolute path.
  bool get isAbsolute => root != null;

  factory _ParsedPath.parse(String path) {
    var root = '/';
    var isRootRelative = false;
    if (root != null) path = path.substring(root.length);

    // Split the parts on path separators.
    var parts = <String>[];
    var separators = <String>[];

    var start = 0;

    if (path.isNotEmpty && _isSeparator(path.codeUnitAt(0))) {
      separators.add(path[0]);
      start = 1;
    } else {
      separators.add('');
    }

    for (var i = start; i < path.length; i++) {
      if (_isSeparator(path.codeUnitAt(i))) {
        parts.add(path.substring(start, i));
        separators.add(path[i]);
        start = i + 1;
      }
    }

    // Add the final part, if any.
    if (start < path.length) {
      parts.add(path.substring(start));
      separators.add('');
    }

    return new _ParsedPath._(root, isRootRelative, parts, separators);
  }

  _ParsedPath._(this.root, this.isRootRelative, this.parts, this.separators);

  String get basename {
    var copy = this.clone();
    copy.removeTrailingSeparators();
    if (copy.parts.isEmpty) return root == null ? '' : root;
    return copy.parts.last;
  }

  String get basenameWithoutExtension => _splitExtension()[0];

  bool get hasTrailingSeparator =>
      !parts.isEmpty && (parts.last == '' || separators.last != '');

  void removeTrailingSeparators() {
    while (!parts.isEmpty && parts.last == '') {
      parts.removeLast();
      separators.removeLast();
    }
    if (separators.length > 0) separators[separators.length - 1] = '';
  }

  void normalize({bool canonicalize: false}) {
    // Handle '.', '..', and empty parts.
    var leadingDoubles = 0;
    var newParts = <String>[];
    for (var part in parts) {
      if (part == '.' || part == '') {
        // Do nothing. Ignore it.
      } else if (part == '..') {
        // Pop the last part off.
        if (newParts.length > 0) {
          newParts.removeLast();
        } else {
          // Backed out past the beginning, so preserve the "..".
          leadingDoubles++;
        }
      } else {
        newParts.add(part);
      }
    }

    // A relative path can back out from the start directory.
    if (!isAbsolute) {
      newParts.insertAll(0, new List.filled(leadingDoubles, '..'));
    }

    // If we collapsed down to nothing, do ".".
    if (newParts.length == 0 && !isAbsolute) {
      newParts.add('.');
    }

    // Canonicalize separators.
    var newSeparators =
        new List<String>.generate(newParts.length, (_) => '/', growable: true);
    newSeparators.insert(0,
        isAbsolute && newParts.length > 0 && _needsSeparator(root) ? '/' : '');

    parts = newParts;
    separators = newSeparators;

    removeTrailingSeparators();
  }

  String toString() {
    var builder = new StringBuffer();
    if (root != null) builder.write(root);
    for (var i = 0; i < parts.length; i++) {
      builder.write(separators[i]);
      builder.write(parts[i]);
    }
    builder.write(separators.last);

    return builder.toString();
  }

  /// Splits the last non-empty part of the path into a `[basename, extension`]
  /// pair.
  ///
  /// Returns a two-element list. The first is the name of the file without any
  /// extension. The second is the extension or "" if it has none.
  List<String> _splitExtension() {
    var file = parts.lastWhere((p) => p != '', orElse: () => null as String);

    if (file == null) return ['', ''];
    if (file == '..') return ['..', ''];

    var lastDot = file.lastIndexOf('.');

    // If there is no dot, or it's the first character, like '.bashrc', it
    // doesn't count.
    if (lastDot <= 0) return [file, ''];

    return [file.substring(0, lastDot), file.substring(lastDot)];
  }

  _ParsedPath clone() => new _ParsedPath._(
      root, isRootRelative, new List.from(parts), new List.from(separators));
}
