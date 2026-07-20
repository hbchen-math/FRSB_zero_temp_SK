.PHONY: update cache build check audit-tex

update:
	lake update

cache:
	lake exe cache get

build:
	lake build

check: build
	bash scripts/check_placeholders.sh

audit-tex:
	bash scripts/audit_tex_labels.sh
