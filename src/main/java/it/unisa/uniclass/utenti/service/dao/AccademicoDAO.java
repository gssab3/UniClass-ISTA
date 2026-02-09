package it.unisa.uniclass.utenti.service.dao;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import jakarta.ejb.Stateless;
import jakarta.persistence.*;
import java.util.List;

@Stateless(name = "AccademicoDAO")
public class AccademicoDAO implements AccademicoRemote {

    @PersistenceContext(unitName = "DBUniClassPU")
    private EntityManager em;

    @Override
    public void create(Accademico accademico) {
        em.persist(accademico);
    }

    @Override
    public void update(Accademico accademico) {
        em.merge(accademico);
    }

    @Override
    public void remove(Accademico accademico) {
        if (!em.contains(accademico)) {
            accademico = em.merge(accademico);
        }
        em.remove(accademico);
    }

    @Override
    public List<Accademico> findByRole(Ruolo ruolo) {
        return em.createNamedQuery("Accademico.findByRuolo", Accademico.class)
                .setParameter("ruolo", ruolo)
                .getResultList();
    }

    @Override
    public List<Accademico> findByRuoloAndDipartimento(Ruolo ruolo, String dipartimento) {
        return em.createNamedQuery("Accademico.findByRuoloAndDip", Accademico.class)
                .setParameter("ruolo", ruolo)
                .setParameter("dipartimento", dipartimento)
                .getResultList();
    }

    @Override
    public List<Accademico> findAll() {
        return em.createNamedQuery("Accademico.findAll", Accademico.class)
                .getResultList();
    }
}