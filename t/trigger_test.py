from .base_test import BaseTest
from testgres.exceptions import QueryException
import re

class TriggerTest(BaseTest):
	def test_self_modified_update_deleted(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1 (
				val_1 int,
				val_2 int
			) USING orioledb;
			INSERT INTO o_test_1 (val_1, val_2)
					(SELECT val_1, 1 FROM generate_series (1, 2) val_1);
			CREATE OR REPLACE FUNCTION func_trig_o_test_11()
			RETURNS TRIGGER AS
			$$
			BEGIN
				DELETE FROM o_test_1 WHERE val_1 = OLD.val_1;
				RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';
		""")
		self.assertEqual(node.execute("""
							SELECT * FROM o_test_1 ORDER BY val_1 ASC;
						 """),
						 [(1, 1), (2, 1)])
		node.safe_psql("""
			CREATE TRIGGER trig_o_test_11 BEFORE UPDATE
				ON o_test_1 FOR EACH ROW
				EXECUTE PROCEDURE func_trig_o_test_11();
		""")
		self.assertEqual(node.execute("""
							SELECT * FROM o_test_1 ORDER BY val_1 ASC;
						 """),
						 [(1, 1), (2, 1)])
		with self.assertRaises(QueryException) as e:
			node.safe_psql("""
				UPDATE o_test_1 SET val_1 = val_1 + 1000 WHERE val_1 % 2 = 0;
			""")
		self.assertErrorMessageEquals(e, "tuple to be updated was already "
										 "modified by an operation triggered "
										 "by the current command",
									   "Consider using an AFTER trigger "
									   "instead of a BEFORE trigger to "
									   "propagate changes to other rows.")
		self.assertEqual(node.execute("""
							SELECT * FROM o_test_1 ORDER BY val_1 ASC;
						 """),
						 [(1, 1), (2, 1)])

	def test_self_modified_delete_updated(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1 (
				val_1 int,
				val_2 int
			) USING orioledb;
			INSERT INTO o_test_1 (val_1, val_2)
					(SELECT val_1, 1 FROM generate_series (1, 2) val_1);
			CREATE OR REPLACE FUNCTION func_trig_o_test_1()
			RETURNS TRIGGER AS
			$$
			BEGIN
				UPDATE o_test_1 SET val_2 = OLD.val_2;
				RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';
		""")
		self.assertEqual(node.execute("""
							SELECT * FROM o_test_1 ORDER BY val_1 ASC;
						 """),
						 [(1, 1), (2, 1)])
		node.safe_psql("""
			CREATE TRIGGER trig_o_test_1 BEFORE DELETE
				ON o_test_1 FOR EACH ROW
				EXECUTE PROCEDURE func_trig_o_test_1();
		""")
		self.assertEqual(node.execute("""
							SELECT * FROM o_test_1 ORDER BY val_1 ASC;
						 """),
						 [(1, 1), (2, 1)])
		with self.assertRaises(QueryException) as e:
			node.safe_psql("""
				DELETE FROM o_test_1 WHERE val_2 % 1 = 0;
			""")
		self.assertErrorMessageEquals(e, "tuple to be deleted was already "
										 "modified by an operation triggered "
										 "by the current command",
									   "Consider using an AFTER trigger "
									   "instead of a BEFORE trigger to "
									   "propagate changes to other rows.")
		self.assertEqual(node.execute("""
							SELECT * FROM o_test_1 ORDER BY val_1 ASC;
						 """),
						 [(1, 1), (2, 1)])

	def test_1(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1(
				val_1 int,
				val_2 int
			)USING orioledb;

			INSERT INTO o_test_1 (val_1, val_2)
				(SELECT val_1, val_1 + 100 FROM generate_series (1, 50) val_1);

			CREATE OR REPLACE FUNCTION func_trig_o_test_1()
			RETURNS TRIGGER AS
			$$
			BEGIN
			INSERT INTO o_test_1(val_1)
				VALUES (OLD.val_1);
			RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';

			CREATE TRIGGER trig_o_test_1 AFTER DELETE
			ON o_test_1 FOR EACH ROW
			EXECUTE PROCEDURE func_trig_o_test_1();

			DELETE FROM o_test_1 WHERE val_2 % 10 = 0;
		""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_2(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1(
				val_1 int,
				val_2 int
			)USING orioledb;
			CREATE TABLE o_test_2(
				val_3 int,
				val_4 int
			)USING orioledb;

			INSERT INTO o_test_1 (val_1, val_2)
				(SELECT val_1, val_1 + 100 FROM generate_series (1, 50) val_1);
			INSERT INTO o_test_2 (val_3, val_4)
				(SELECT val_3, val_3 + 100 FROM generate_series (1, 50) val_3);

			CREATE OR REPLACE FUNCTION func_trig_o_test_1()
			RETURNS TRIGGER AS
			$$
			BEGIN
			INSERT INTO o_test_1(val_1)
				VALUES (OLD.val_1);

			RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';

			CREATE TRIGGER trig_o_test_12 AFTER DELETE
			ON o_test_1 FOR EACH ROW
			EXECUTE PROCEDURE func_trig_o_test_1();

			DELETE FROM o_test_1 WHERE val_1 = 2;
		""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_3(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1(
				val_1 int,
				val_2 int,
				val_22 int
			)USING orioledb;
			CREATE TABLE o_test_2(
				val_3 int,
				val_4 int
			)USING orioledb;

			INSERT INTO o_test_1 (val_1, val_2, val_22)
				(SELECT val_1, val_1 + 100, val_1 + 20 FROM generate_series (1, 50) val_1);
			INSERT INTO o_test_2 (val_3, val_4)
				(SELECT val_3, val_3 + 100 FROM generate_series (1, 50) val_3);

			CREATE OR REPLACE FUNCTION func_trig_o_test_1()
			RETURNS TRIGGER AS
			$$
			BEGIN
			INSERT INTO o_test_1(val_1)
				VALUES (OLD.val_1);
			RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';

			CREATE TRIGGER trig_o_test_1 BEFORE DELETE
			ON o_test_1 FOR EACH ROW
			EXECUTE PROCEDURE func_trig_o_test_1();

			UPDATE o_test_1 SET val_1 = val_1 + 100;

			DELETE FROM o_test_1 WHERE val_22 % 10 = 0;
		""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_4(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1(
				val_1 int,
				val_2 int
			)USING orioledb;

			INSERT INTO o_test_1 (val_1, val_2)
				(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

			CREATE OR REPLACE FUNCTION func_trig_o_test_1()
			RETURNS TRIGGER AS
			$$
			BEGIN
			INSERT INTO o_test_1(val_1)
				VALUES (OLD.val_1);
			RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';

			CREATE TRIGGER trig_o_test_1 AFTER DELETE
			ON o_test_1 FOR EACH STATEMENT
			EXECUTE PROCEDURE func_trig_o_test_1();

			DELETE FROM o_test_1 WHERE val_1 = 3;
		""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_5(self):
		node = self.node
		node.start()
		node.safe_psql("""
			CREATE EXTENSION IF NOT EXISTS orioledb;
			CREATE TABLE o_test_1(
				val_1 int,
				val_2 int
			)USING orioledb;

			INSERT INTO o_test_1 (val_1, val_2)
				(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

			CREATE OR REPLACE FUNCTION func_trig_o_test_1()
			RETURNS TRIGGER AS
			$$
			BEGIN
			INSERT INTO o_test_1(val_1)
				VALUES (OLD.val_1);
			RETURN OLD;
			END;
			$$
			LANGUAGE 'plpgsql';

			CREATE TRIGGER trig_o_test_1 AFTER UPDATE
			ON o_test_1 FOR EACH STATEMENT
			EXECUTE PROCEDURE func_trig_o_test_1();

			UPDATE o_test_1 SET val_1 = val_1 + 100;
		""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_7(self):
		node = self.node
		node.start()
		with self.assertRaises(QueryException) as e:
			node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1 (val_1, val_2)USING orioledb
					AS (SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_trig_1()
				RETURNS event_trigger
				LANGUAGE plpgsql
				AS $$
				BEGIN
				RAISE EXCEPTION 'command % is disabled', tg_tag;
				END;
				$$;

				CREATE EVENT TRIGGER trig_1 ON ddl_command_start
				EXECUTE FUNCTION func_trig_1();

				CREATE TABLE o_test_2 (val_3, val_4)USING orioledb
					AS (SELECT * FROM o_test_1);
			""")

		self.assertEqual(e.exception.message,
						 "ERROR:  command CREATE TABLE AS is disabled\n" +
						 "CONTEXT:  PL/pgSQL function func_trig_1() line 3 at RAISE\n"
						 "CONTEXT:  PL/pgSQL function func_trig_1() line 3 at RAISE\n")

		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_8(self):
		node = self.node
		node.start()
		with self.assertRaises(QueryException) as e:
			node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1 (val_1, val_2)USING orioledb
					AS (SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_trig_1()
				RETURNS event_trigger
				LANGUAGE plpgsql
				AS $$
				BEGIN
				RAISE EXCEPTION 'command % is disabled', tg_tag;
				END;
				$$;

				CREATE EVENT TRIGGER trig_1 ON ddl_command_end
				EXECUTE FUNCTION func_trig_1();

				CREATE TABLE o_test_2 (val_3, val_4)USING orioledb
					AS (SELECT * FROM o_test_1);
			""")

		self.assertEqual(e.exception.message,
						 "ERROR:  command CREATE TABLE AS is disabled\n" +
						 "CONTEXT:  PL/pgSQL function func_trig_1() line 3 at RAISE\n")


		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_9(self):
		node = self.node
		node.start()
		with self.assertRaises(QueryException) as e:
			node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				CREATE OR REPLACE FUNCTION func_trig_o_test_1()
				RETURNS TRIGGER AS
				$$
				BEGIN
				INSERT INTO o_test_1(val_1)
					VALUES (OLD.val_1);
				DELETE FROM o_test_1 WHERE val_1 = OLD.val_1;
				RETURN OLD;
				END;
				$$
				LANGUAGE 'plpgsql';

				INSERT INTO o_test_1 (val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 1) val_1);

				CREATE TRIGGER trig_o_test_1 AFTER UPDATE
					ON o_test_1 FOR EACH ROW
					EXECUTE PROCEDURE func_trig_o_test_1();

				CREATE TRIGGER trig_o_test_6 BEFORE DELETE
					ON o_test_1 FOR EACH ROW
					EXECUTE PROCEDURE func_trig_o_test_1();

				UPDATE o_test_1 SET val_2 = val_2 + 111;
			""")

		m=[x.group(0) for x in list(re.finditer(r'.*\n', e.exception.message))[0:3]]
		self.assertEqual("".join(m),
						"ERROR:  stack depth limit exceeded\n" +
						"HINT:  Increase the configuration parameter \"max_stack_depth\" (currently 2048kB), after ensuring the platform's stack depth limit is adequate.\n" +
						"CONTEXT:  SQL statement \"DELETE FROM o_test_1 WHERE val_1 = OLD.val_1\"\n")

		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_10(self):
		node = self.node
		node.start()
		with self.assertRaises(QueryException) as e:
			node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1 (val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_trig_o_test_1()
				RETURNS TRIGGER AS
				$$
				BEGIN
				INSERT INTO o_test_1(val_1)
					VALUES (OLD.val_1);
				RETURN OLD;
				END;
				$$
				LANGUAGE 'plpgsql';

				CREATE TRIGGER trig_o_test_1 AFTER INSERT
				ON o_test_1 FOR EACH STATEMENT
				EXECUTE PROCEDURE func_trig_o_test_1();

				INSERT INTO o_test_1 (val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);
			""")

		m=[x.group(0) for x in list(re.finditer(r'.*\n', e.exception.message))[0:3]]
		self.assertEqual("".join(m),
						"ERROR:  stack depth limit exceeded\n" +
						"HINT:  Increase the configuration parameter \"max_stack_depth\" (currently 2048kB), after ensuring the platform's stack depth limit is adequate.\n" +
						"CONTEXT:  SQL statement \"INSERT INTO o_test_1(val_1)\n")

		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_11(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_NAME = 'trig_1') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_2
					AFTER INSERT ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				UPDATE o_test_1 SET val_2 = val_2 + 100;

				INSERT INTO o_test_1(val_1, val_2)
					VALUES (1, 1);
		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,201), (2,202),
			(3,203), (4,204), (5,205), (1, None), (2, None), (3, None), (4, None),
			(5, None), (1,1)])

		node.stop()

	def test_12(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_NAME = 'trig_1') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_2
					AFTER INSERT ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				INSERT INTO o_test_1(val_1, val_2)
					VALUES (1, 1);
		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105), (1,1)])

		node.stop()

	def test_13(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_NAME = 'trig_1') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						ELSIF (TG_NAME = 'trig_2') THEN
							DELETE FROM o_test_1 WHERE val_2 = NEW.val_2;
						ELSIF (TG_NAME = 'trig_3') THEN
							DELETE FROM o_test_1 WHERE val_2 = NEW.val_2;
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_2
					BEFORE UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_3
					BEFORE UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				UPDATE o_test_1 SET val_2 = val_2 + 100;

		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105)])

		node.stop()

	def test_14(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_WHEN = 'BEFORE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						ELSIF (TG_WHEN = 'AFTER') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_2
					BEFORE UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				UPDATE o_test_1 SET val_2 = val_2 + 100;

		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105), (1, None), (2, None), (3, None), (4, None),
			(5, None)])

		node.stop()

	def test_15(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_WHEN = 'BEFORE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_2
					BEFORE UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				UPDATE o_test_1 SET val_2 = val_2 + 100;

		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105), (1, None), (2, None), (3, None), (4, None),
			(5, None)])

		node.stop()

	def test_16(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_WHEN = 'AFTER') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_2
					BEFORE DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				DELETE FROM o_test_1 WHERE val_1 = 1;

		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105)])

		node.stop()

	def test_17(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_LEVEL = 'ROW') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						ELSIF
						(TG_LEVEL = 'STATEMENT') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_2
					BEFORE UPDATE ON o_test_1
					FOR EACH STATEMENT EXECUTE FUNCTION func_1();

				DELETE FROM o_test_1 WHERE val_2 = 1;

				UPDATE o_test_1 SET val_2 = val_2 + 100;

		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,201), (2,202),
			(3,203), (4,204), (5,205), (None, None)])

		node.stop()

	def test_18(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_OP = 'INSERT') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (OLD.val_1);
						ELSIF (TG_OP = 'UPDATE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						ELSIF (TG_OP = 'TRUNCATE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						ELSIF (TG_OP = 'DELETE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					BEFORE DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				DELETE FROM o_test_1 WHERE val_2 = 1;
		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105)])

		node.stop()

	def test_19(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_OP = 'UPDATE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE OR REPLACE FUNCTION func_2() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_OP = 'DELETE') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					BEFORE UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				CREATE TRIGGER trig_2
					BEFORE DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_2();

				DELETE FROM o_test_1 WHERE val_2 = 1;

				UPDATE o_test_1 SET val_2 = val_2 + 100;
		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105), (1, None), (2, None), (3, None), (4, None),
			(5, None)])

		node.stop()

	def test_20(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_RELID = 'o_test_1'::regclass) THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					BEFORE UPDATE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				UPDATE o_test_1 SET val_2 = val_2 + 100;
		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105)])

		node.stop()

	def test_21(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_TABLE_NAME = 'o_test_1') THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				DELETE FROM o_test_1 WHERE val_1 = 1;
		""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()

	def test_22(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				INSERT INTO o_test_1(val_1, val_2)
					(SELECT val_1, val_1 + 100 FROM generate_series (1, 5) val_1);

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_NARGS = 0) THEN
							INSERT INTO o_test_1(val_1)
								VALUES (NEW.val_1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					BEFORE DELETE ON o_test_1
					FOR EACH ROW EXECUTE FUNCTION func_1();

				DELETE FROM o_test_1 WHERE val_1 = 1;
		""")
		node.stop(['-m', 'immediate'])

		node.start()

		self.assertEqual(node.execute("SELECT * FROM o_test_1"), [(1,101), (2,102),
			(3,103), (4,104), (5,105), (None, None)])

		node.stop()

	def test_23(self):
		node = self.node
		node.start()
		node.safe_psql("""
				CREATE EXTENSION IF NOT EXISTS orioledb;

				CREATE TABLE o_test_1(
					val_1 int,
					val_2 int
				)USING orioledb;

				CREATE TABLE o_test_2(
					val_3 int,
					val_4 int
				)USING orioledb;

				CREATE OR REPLACE FUNCTION func_1() RETURNS TRIGGER AS $$
					BEGIN
						IF (TG_OP = 'INSERT') THEN
							INSERT INTO o_test_2(val_3, val_4)
								VALUES (1, 1);
						END IF;
						RETURN NULL;
					END;
				$$ LANGUAGE plpgsql;

				CREATE TRIGGER trig_1
					AFTER INSERT ON o_test_1
					REFERENCING NEW TABLE AS new_table
					FOR EACH STATEMENT EXECUTE FUNCTION func_1();
				CREATE TRIGGER trig_2
					AFTER UPDATE ON o_test_1
					REFERENCING OLD TABLE AS old_table NEW TABLE AS new_table
					FOR EACH STATEMENT EXECUTE FUNCTION func_1();
				CREATE TRIGGER trig_3
					AFTER DELETE ON o_test_1
					REFERENCING OLD TABLE AS old_table
					FOR EACH STATEMENT EXECUTE FUNCTION func_1();

				INSERT INTO o_test_1(val_1, val_2)
					VALUES (1, 1);

				UPDATE o_test_1 SET val_2 = val_2 + 100;

				DELETE FROM o_test_1 WHERE val_2 = 1;
				""")
		node.stop(['-m', 'immediate'])

		node.start()
		node.stop()




