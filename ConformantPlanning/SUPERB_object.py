from sample import call_SMT_solver
from sampleGenerator import sampleGenerator
from tag import Tag
from z3 import *



class SUPERB_object:
    def __init__(self):
        self.tag_history = list()#[[(set()]一号tag的历史, set[set()]二号tag的历史]

    def improve_counter_example(self, counter_example, contexts, old_sample_generator): # 由于之前context和tag的位置都是固定的，所以tag_history中每个元素的位置也是固定的，可以不必要刻意寻找具体位置
        tags = Tag(counter_example, contexts).get_tags()
        if len(self.tag_history) == 0:
            for tag in tags:
                self.tag_history.append([tag])
            return counter_example
        res = None
        can_be_improved = True
        new_sample_generator = sampleGenerator(None, None, None, type='object')
        new_sample_generator.constraint_object = old_sample_generator.constraint_object
        new_sample_generator.solver.add(old_sample_generator.constraint_list)
        while can_be_improved:
            new_tags, old_tags, can_be_improved = self.compare_tags(tags)
            if can_be_improved:
                self.keep_new_tags(new_sample_generator, new_tags)
                self.remove_old_tags(new_sample_generator, old_tags)
                new_counter_example = new_sample_generator.call_SMT_solver()
                if new_counter_example is None:
                    break
                else:
                    res = new_counter_example
                tags = Tag(new_counter_example, contexts).get_tags()
        for i in range(len(tags)):
            self.tag_history[i].append(tags[i])
        if res is None:
            return counter_example
        else:
            return res

    def keep_new_tags(self, sample_generator, new_tags):
        for tag in new_tags:
            for fact in tag:
                bool_item = sample_generator.constraint_object.Atom_to_smt(fact, 0)
                sample_generator.solver.add(bool_item == True)

    def remove_old_tags(self, sample_generator, old_tags):
        for old_tag in old_tags:
            for history_tag in self.tag_history:
                if old_tag in history_tag:
                    for fact_set in history_tag:
                        remove_items = set()
                        if len(fact_set) != 0:
                            for fact in fact_set:
                                bool_item = sample_generator.constraint_object.Atom_to_smt(fact, 0)
                                remove_items.add(bool_item)
                        sample_generator.solver.add(Not(And(remove_items)))

    def generate_new_counter_example(self, constraint):
        new_counter_example, _ = call_SMT_solver(constraint)
        return new_counter_example

    def compare_tags(self, tag_list):
        new_tags = list()
        old_tags = list()
        can_be_improved = False
        for i in range(len(tag_list)):
            if len(tag_list[i]) != 0:
                if tag_list[i] not in self.tag_history[i]:  # 某个tag是全新的tag
                    new_tags.append(tag_list[i])
                else:
                    old_tags.append(tag_list[i])
                    can_be_improved = True
        return new_tags, old_tags, can_be_improved

