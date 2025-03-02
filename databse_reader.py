
import sqlite3

conn = sqlite3.connect("db.sqlite3")
cursor = conn.cursor()
sql = "select * from pCPCES_task"
cursor.execute(sql)
result = cursor.fetchall()
print(result)
print(type(result))
conn.close()
