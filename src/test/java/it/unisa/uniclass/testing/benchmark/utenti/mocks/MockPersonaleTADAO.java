package it.unisa.uniclass.testing.benchmark.utenti.mocks;

import it.unisa.uniclass.utenti.model.PersonaleTA;

import java.util.*;

public class MockPersonaleTADAO implements PersonaleTARemote {

    // archivio interno più realistico
    private final Map<String, PersonaleTA> byEmail = new HashMap<>();
    private PersonaleTA personaleDaRitornare;

    public void add(PersonaleTA p) {
        byEmail.put(p.getEmail(), p);
    }
    // Questo metodo deve essere visibile
    public void setPersonaleDaRitornare(PersonaleTA p) {
        this.personaleDaRitornare = p;
    }
    public void clear() {
        byEmail.clear();
    }

    @Override
    public PersonaleTA trovaEmail(String email) {
        return byEmail.getOrDefault(email, null);
    }

    @Override
    public PersonaleTA trovaEmailPassword(String email, String password) {
        PersonaleTA p = byEmail.get(email);
        if (p != null && Objects.equals(p.getPassword(), password)) {
            return p;
        }
        return null;
    }

    @Override
    public PersonaleTA trovaPersonale(long id) {
        return null;
    }

    @Override
    public List<PersonaleTA> trovaTutti() {
        return new ArrayList<>(byEmail.values());
    }

    @Override
    public void aggiungiPersonale(PersonaleTA p) { }

    @Override
    public void rimuoviPersonale(PersonaleTA p) { }
}
