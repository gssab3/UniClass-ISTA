package it.unisa.uniclass.utenti.service.dao;

import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.ejb.Stateless;
import jakarta.persistence.*;

import java.util.List;

@Stateless(name = "AccademicoDAO")
public class AccademicoDAO implements AccademicoRemote {

    @PersistenceContext(unitName = "DBUniClassPU")
    private EntityManager emUniclass;

    @Override
    public void create(Accademico accademico) {
        emUniclass.persist(accademico);
    }

    @Override
    public void update(Accademico accademico) {
        emUniclass.merge(accademico);
    }

    @Override
    public void remove(Accademico accademico) {
        if (!emUniclass.contains(accademico)) {
            accademico = emUniclass.merge(accademico);
        }
        emUniclass.remove(accademico);
    }

    @Override
    public Accademico findByEmail(String email) {
        return emUniclass.find(Accademico.class, email);
    }

    @Override
    public List<Accademico> findByRole(Ruolo ruolo){
        vai vai queto

}


}