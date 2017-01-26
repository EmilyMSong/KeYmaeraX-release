ALTER TABLE users ADD COLUMN level INTEGER DEFAULT 0;
ALTER TABLE models ADD COLUMN isTemporary INTEGER DEFAULT 0;
ALTER TABLE proofs ADD COLUMN lemmaId INTEGER;
ALTER TABLE proofs ADD COLUMN isTemporary INTEGER DEFAULT 0;
UPDATE users SET level=0;
UPDATE models SET isTemporary=0;
UPDATE proofs SET isTemporary=0;
UPDATE config SET value="4.3.2" WHERE configName="version" AND key="version";