"""Package the new revision with the existing exact inventory/byte gate."""
import argparse
from pathlib import Path
import package_dh_controls as packaging
from verify_figure_revision import ROOT,MANIFEST,run


def configure():
    # Scope is this process; historical source/manifest bytes are unchanged.
    packaging.ROOT=ROOT;packaging.MANIFEST=MANIFEST;packaging.run=run


def verify_bundle(path,manifest=None):
    configure();return packaging.verify_bundle(path,manifest)


def package(path):
    configure();return packaging.package(path)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'tmp/release-figures-2026-10-16/dh-controls-2026-10-15.tar.gz')
    package(p.parse_args().output)
