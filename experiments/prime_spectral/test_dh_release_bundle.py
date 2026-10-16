"""A stale supplied bundle must be rejected before any remote draft action."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import package_dh_controls as packaging


class BundleGateChecks(unittest.TestCase):
    def exercise(self,stale):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'paper').mkdir();(root/'paper/DH_CONTROLS_REPRODUCTION.md').write_text('Guide\n')
            (root/'data.json').write_text('{"accepted":true}\n')
            manifest={'artifacts_sha256':{n:packaging.sha(root/n) for n in ['data.json','paper/DH_CONTROLS_REPRODUCTION.md']}}
            m=root/'manifest.json';m.write_text(json.dumps(manifest))
            path=root/'bundle.tar.gz'
            with tarfile.open(path,'w:gz') as archive:
                for name in ['data.json','paper/DH_CONTROLS_REPRODUCTION.md','manifest.json','README.md']:
                    content=(root/('paper/DH_CONTROLS_REPRODUCTION.md' if name=='README.md' else name)).read_bytes()
                    if stale and name=='data.json':content=b'{"accepted":false}\n'
                    info=tarfile.TarInfo('dh-controls-2026-10-15/'+name);info.size=len(content)
                    archive.addfile(info,io.BytesIO(content))
            with patch.object(packaging,'ROOT',root),patch.object(packaging,'MANIFEST',m):
                if stale:
                    with self.assertRaisesRegex(ValueError,'archive byte mismatch'):
                        packaging.verify_bundle(path,manifest)
                else:self.assertEqual(packaging.verify_bundle(path,manifest)['members'],4)

    def test_matching_bundle_accepted(self):self.exercise(False)
    def test_stale_bundle_rejected(self):self.exercise(True)


if __name__=='__main__':unittest.main()
