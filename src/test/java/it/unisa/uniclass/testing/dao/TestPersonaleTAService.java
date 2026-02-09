package it.unisa.uniclass.testing.dao;

import it.unisa.uniclass.utenti.model.PersonaleTA;

public class TestPersonaleTAService extends PersonaleTAService {
    private PersonaleTARemote personaleTADao;

    public TestPersonaleTAService() {}

    public void setPersonaleTADao(PersonaleTARemote personaleTADao) {
        this.personaleTADao = personaleTADao;
    }

    @Override
    public PersonaleTA trovaEmailPass(String email, String pass) {
        return personaleTADao.trovaEmailPassword(email, pass);
    }
}