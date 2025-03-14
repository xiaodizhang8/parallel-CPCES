# Generated by Django 3.2.8 on 2024-03-03 06:02

from django.db import migrations, models
import django.db.models.deletion


class Migration(migrations.Migration):

    initial = True

    dependencies = [
    ]

    operations = [
        migrations.CreateModel(
            name='Task',
            fields=[
                ('id', models.BigAutoField(auto_created=True, primary_key=True, serialize=False, verbose_name='ID')),
                ('domain_name', models.CharField(max_length=200, verbose_name='Domain Name')),
                ('instance_name', models.CharField(max_length=200, verbose_name='Instance Name')),
                ('probability_threshold', models.FloatField(verbose_name='Probability Threshold')),
                ('status', models.IntegerField(choices=[(1, 'waiting'), (2, 'started'), (3, 'finished'), (4, 'cancelled')], verbose_name='Task Status')),
                ('plan', models.TextField(null=True, verbose_name='Plan')),
                ('searching_time', models.FloatField(null=True, verbose_name='Searching Time')),
                ('domain_path', models.TextField(verbose_name='Domain Path')),
                ('instance_path', models.TextField(verbose_name='Instance Path')),
                ('update_time', models.DateTimeField(auto_now=True)),
            ],
        ),
        migrations.CreateModel(
            name='WorkerTask',
            fields=[
                ('id', models.BigAutoField(auto_created=True, primary_key=True, serialize=False, verbose_name='ID')),
                ('iteration', models.IntegerField(verbose_name='Iteration')),
                ('classical_domain_name', models.CharField(max_length=200, verbose_name='Classical Domain Name')),
                ('classical_instance_name', models.CharField(max_length=200, verbose_name='Classical Instance Name')),
                ('weight', models.FloatField(verbose_name='Weight')),
                ('status', models.IntegerField(choices=[(1, 'waiting'), (2, 'started'), (3, 'finished'), (4, 'cancelled')], verbose_name='Task Status')),
                ('hitting_set_index', models.TextField(verbose_name='Hitting Set Index')),
                ('plan', models.TextField(null=True, verbose_name='Plan')),
                ('searching_time', models.FloatField(null=True, verbose_name='Searching Time')),
                ('classical_domain_path', models.TextField(verbose_name='Classical Domain Path')),
                ('classical_instance_path', models.TextField(verbose_name='Classical Instance Path')),
                ('update_time', models.DateTimeField(auto_now=True)),
                ('task', models.ForeignKey(on_delete=django.db.models.deletion.PROTECT, to='pCPCES.task')),
            ],
        ),
    ]
